import requests
import time
import os
import re
import sys
import tempfile
import subprocess
import json
from rich.progress import Progress
import polars as pl

# Handle imports for both script and package usage
try:
    from .eval_utils import (
        PROTO_REPOS,
        JSON_REPOS,
        locate_pollux,
        paginated_github_query,
    )
except ImportError:
    from eval_utils import (
        PROTO_REPOS,
        JSON_REPOS,
        locate_pollux,
        paginated_github_query,
    )


def search_popular_go_repositories(github_token: str):
    """
    Search for popular Go repositories on GitHub.

    Args:
        github_token: GitHub personal access token for authentication.

    Returns:
        List of dictionaries containing repository information.
    """
    headers = {
        "Authorization": f"token {github_token}",
        "Accept": "application/vnd.github.v3+json",
    }
    search_url = (
        "https://api.github.com/search/repositories?q=language:go&sort=stars&order=desc"
    )

    repos = paginated_github_query(search_url, headers)
    repos = [
        {
            "owner": repo["owner"]["login"],
            "name": repo["name"],
            "stars": repo["stargazers_count"],
        }
        for page in repos
        for repo in page["items"]
    ]
    return repos


def get_json_usage_parquet(
    owner: str, repo: str, github_token: str, output_filename: str | None = None
):
    """
    Check if a repository contains Go code with JSON struct tags.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        github_token: GitHub personal access token.
        output_filename: Optional path to save the parquet file.
    """
    headers = {
        "Authorization": f"token {github_token}",
        "Accept": "application/vnd.github.v3+json",
    }

    search_url = f"https://api.github.com/search/code?q=repo:{owner}/{repo}+language:go+json%3A%22"

    json_go_results = paginated_github_query(search_url, headers)
    json_go_files = [
        {"owner": owner, "repo": repo, "file": file["path"]}
        for page in json_go_results
        for file in page["items"]
    ]

    if output_filename is not None and len(json_go_files) > 0:
        df = pl.DataFrame(json_go_files)
        df.write_parquet(output_filename)


def get_json_usage_parquet_local(
    owner: str,
    repo: str,
    output_filename: str,
    cache_dir: str | None = None,
    error_log: str | None = None,
) -> None:
    """
    Clones a repository locally to extract Go files with JSON struct tags.
    This bypasses GitHub API limits for large repositories.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        output_filename: Path to save the parquet file.
        cache_dir: Optional cache directory path. If provided, repos are cached as <owner>-<repo>.
                   If None, uses temporary directory.
        error_log: Optional path to log errors to disk.
    """
    repo_url = f"https://github.com/{owner}/{repo}.git"
    repo_name = f"{owner}-{repo}"

    if cache_dir:
        os.makedirs(cache_dir, exist_ok=True)
        repo_path = os.path.join(cache_dir, repo_name)

        if os.path.exists(repo_path):
            print(f"Using cached repository at {repo_path}")
            try:
                print(f"Updating cached repository...")
                _ = subprocess.run(
                    ["git", "-C", repo_path, "fetch", "--all"],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                _ = subprocess.run(
                    ["git", "-C", repo_path, "reset", "--hard", "origin/HEAD"],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error updating cached repository: {e}")
                print(f"Will try to use cached version as-is")
        else:
            print(f"Cloning {repo_url} to cache...")
            try:
                _ = subprocess.run(
                    ["git", "clone", repo_url, repo_path],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error cloning repository: {e}")
                return

        _process_json_repo_for_stats(owner, repo, repo_path, output_filename, error_log)
    else:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_path = os.path.join(temp_dir, repo)

            print(f"Cloning {repo_url}...")
            try:
                _ = subprocess.run(
                    ["git", "clone", repo_url, repo_path],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error cloning repository: {e}")
                return

            _process_json_repo_for_stats(
                owner, repo, repo_path, output_filename, error_log
            )


def _process_json_repo_for_stats(
    owner: str,
    repo: str,
    repo_path: str,
    output_filename: str,
    error_log: str | None = None,
) -> None:
    """
    Helper function to process a git repository and extract Go files with JSON struct tags.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        repo_path: Path to the cloned repository.
        output_filename: Path to save the parquet file.
        error_log: Optional path to log errors to disk.
    """
    pollux_bin = locate_pollux()

    original_cwd = os.getcwd()

    if error_log:
        error_log = os.path.abspath(error_log)

    output_filename = os.path.abspath(output_filename)

    os.chdir(repo_path)

    try:
        print("Finding Go files with JSON struct tags...")
        # Use grep to efficiently find .go files containing JSON struct tags
        # The -l flag returns only filenames, not the matching lines
        result = subprocess.run(
            [
                "find",
                ".",
                "-name",
                "*.go",
                "-type",
                "f",
                "-exec",
                "grep",
                "-l",
                '`json:"',
                "{}",
                "+",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        json_go_files = [
            f.strip().lstrip("./")
            for f in result.stdout.strip().split("\n")
            if f.strip()
        ]

        njson = len(json_go_files)
        print(f"Found {njson} Go files with JSON struct tags in {owner}/{repo}")

        # Step 3: Convert files to packages (directories)
        # Group by directory since package name is the relative path to the directory
        packages = set()
        for file in json_go_files:
            # Get the directory containing the file
            dir_path = os.path.dirname(file)
            if dir_path == "":
                # File is in root directory
                dir_path = "."
            # Prefix with "./" as required for Go packages
            package_path = "./" + dir_path if dir_path != "." else "."
            packages.add(package_path)

        packages = sorted(list(packages))
        npackages = len(packages)
        print(f"Found {npackages} unique Go packages with JSON struct tags")

        # Step 4: Get commit history for each file
        data_rows = []

        error_log_file = None
        if error_log:
            try:
                error_log_file = open(error_log, "a")
            except IOError as log_err:
                print(f"Failed to open error log file: {log_err}", file=sys.stderr)
                error_log_file = None

        with Progress() as progress:
            task = progress.add_task("[green]Processing Go files...", total=njson)

            for file in json_go_files:
                try:
                    result = subprocess.run(
                        ["git", "log", "--format=%H", "--", file],
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    commit_hashes = [
                        h.strip()
                        for h in result.stdout.strip().split("\n")
                        if h.strip()
                    ]

                    row_data = {
                        "repository": f"{owner}/{repo}",
                        "go_file": file,
                        "commits": commit_hashes,
                        "commit_count": len(commit_hashes),
                    }

                    stats_json = subprocess.run(
                        [pollux_bin, "json", "stats", file],
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    stats = json.loads(stats_json.stdout)

                    if file in stats:
                        # Merge the stats dict into the row
                        row_data.update(stats[file])
                        # skip false positives
                        data_rows.append(row_data)
                    else:
                        print(f"WARN: Skipping false positive: {file}")

                except subprocess.CalledProcessError as e:
                    if e.stderr:
                        print(e.stderr, file=sys.stderr)
                    else:
                        print(
                            f"Command '{' '.join(e.cmd)}' returned non-zero exit status {e.returncode}",
                            file=sys.stderr,
                        )

                    if error_log_file:
                        try:
                            error_log_file.write(f"[{owner}/{repo}] ")
                            if e.stderr:
                                error_log_file.write(e.stderr)
                                if not e.stderr.endswith("\n"):
                                    error_log_file.write("\n")
                            else:
                                error_log_file.write(
                                    f"Command '{' '.join(e.cmd)}' returned non-zero exit status {e.returncode}\n"
                                )
                            error_log_file.flush()
                        except IOError as log_err:
                            print(
                                f"Failed to write to error log: {log_err}",
                                file=sys.stderr,
                            )
                except (json.JSONDecodeError, KeyError) as e:
                    error_msg = (
                        f"[{owner}/{repo}] Error parsing pollux stats output: {e}"
                    )
                    print(error_msg, file=sys.stderr)
                    if error_log_file:
                        try:
                            error_log_file.write(f"{error_msg}\n")
                            error_log_file.flush()
                        except IOError:
                            pass

                progress.update(task, advance=1)

        if error_log_file:
            try:
                error_log_file.close()
            except IOError:
                pass

        # Step 6: Save data to parquet file
        df = pl.DataFrame(data_rows)

        # Ensure parent directory exists
        output_dir = os.path.dirname(output_filename)
        if output_dir:
            os.makedirs(output_dir, exist_ok=True)

        df.write_parquet(output_filename)
        print(f"\n\nSaved JSON usage data to {output_filename}")

    finally:
        os.chdir(original_cwd)


def get_proto_history_parquet(
    owner: str, repo: str, github_token: str, output_filename: str
) -> None:
    """
    Fetches the commit history for all .proto files in a GitHub repository
    using the GitHub API and saves the result as a Parquet file.

    Limited to 1000 proto files due to GitHub Search API constraints.
    Use get_proto_history_parquet_local() for larger repositories.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        github_token: GitHub personal access token for authentication.
        output_filename: Path to save the parquet file.
    """
    search_url = (
        f"https://api.github.com/search/code?q=extension:proto+repo:{owner}/{repo}"
    )
    headers = {
        "Authorization": f"token {github_token}",
        "Accept": "application/vnd.github.v3+json",
    }
    proto_files = paginated_github_query(search_url, headers)
    proto_files = [proto["path"] for page in proto_files for proto in page["items"]]
    nproto = len(proto_files)
    print(f"Found {nproto} proto files in {owner}/{repo}")

    data_rows = []

    with Progress() as progress:
        task = progress.add_task("[green]Processing proto files...", total=nproto)

        for file in proto_files:
            commits_url = (
                f"https://api.github.com/repos/{owner}/{repo}/commits?path={file}"
            )
            results = paginated_github_query(commits_url, headers)
            commit_hashes = [commits["sha"] for page in results for commits in page]

            data_rows.append(
                {
                    "repository": f"{owner}/{repo}",
                    "proto_file": file,
                    "commits": commit_hashes,
                    "commit_count": len(commit_hashes),
                }
            )

            progress.update(task, advance=1)
            time.sleep(1)  # Avoid rate limiting

    df = pl.DataFrame(data_rows)
    df.write_parquet(output_filename)
    print(f"\n\nSaved commit history to {output_filename}")


def get_proto_history_parquet_local(
    owner: str,
    repo: str,
    output_filename: str,
    cache_dir: str | None = None,
    error_log: str | None = None,
) -> None:
    """
    Clones a repository locally to extract commit history for all .proto files.
    This bypasses GitHub API limits for large repositories.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        output_filename: Path to save the parquet file.
        cache_dir: Optional cache directory path. If provided, repos are cached as <owner>-<repo>.
                   If None, uses temporary directory.
        error_log: Optional path to log errors to disk.
    """
    repo_url = f"https://github.com/{owner}/{repo}.git"
    repo_name = f"{owner}-{repo}"

    if cache_dir:
        os.makedirs(cache_dir, exist_ok=True)
        repo_path = os.path.join(cache_dir, repo_name)

        if os.path.exists(repo_path):
            print(f"Using cached repository at {repo_path}")
            try:
                print(f"Updating cached repository...")
                _ = subprocess.run(
                    ["git", "-C", repo_path, "fetch", "--all"],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                _ = subprocess.run(
                    ["git", "-C", repo_path, "reset", "--hard", "origin/HEAD"],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error updating cached repository: {e}")
                print(f"Will try to use cached version as-is")
        else:
            print(f"Cloning {repo_url} to cache...")
            try:
                _ = subprocess.run(
                    ["git", "clone", repo_url, repo_path],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error cloning repository: {e}")
                return

        _process_proto_repo_for_stats(
            owner, repo, repo_path, output_filename, error_log
        )
    else:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_path = os.path.join(temp_dir, repo)

            print(f"Cloning {repo_url}...")
            try:
                _ = subprocess.run(
                    ["git", "clone", repo_url, repo_path],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            except subprocess.CalledProcessError as e:
                print(f"Error cloning repository: {e}")
                return

            _process_proto_repo_for_stats(
                owner, repo, repo_path, output_filename, error_log
            )


# A repository is not one protobuf module. Its .proto files sit under
# directories that play the role of protoc's -I, and an import names a file
# relative to one of those rather than to the repository root, so compiling
# everything from the root alone fails on every file whose imports are written
# that way -- which is most of what fails at all in this dataset.
#
# Nothing in a repository declares those directories in a form worth parsing
# (buf.yaml covers buf's own modules but not the testdata that makes up most of
# its .proto files), but the imports themselves say where they are: if some file
# imports "google/rpc/code.proto" and the repository holds
# "third_party/google/rpc/code.proto", then "third_party" is an import path.
# That is the whole of the heuristic below.

IMPORT_RE = re.compile(r'^\s*import\s+(?:public\s+|weak\s+)?"([^"]+)"\s*;', re.M)

# Imports the compiler answers itself, so a root need not hold them.
WELL_KNOWN_PREFIX = "google/protobuf/"

# The repository root, as an import path.
REPO_ROOT = "."


def read_proto_imports(proto_files: list[str]) -> dict[str, list[str]]:
    """
    Reads the import statements out of each file, relative to the working
    directory.

    Args:
        proto_files: Paths of the .proto files, relative to the repository.

    Returns:
        The imported names of each file, keyed by path. A file that cannot be
        read has none, and drops out of the heuristic rather than the dataset.
    """
    imports = {}
    for file in proto_files:
        try:
            with open(file, errors="replace") as fh:
                imports[file] = IMPORT_RE.findall(fh.read())
        except OSError as e:
            print(f"Cannot read {file}: {e}", file=sys.stderr)
            imports[file] = []
    return imports


def discover_import_roots(
    proto_files: list[str], imports: dict[str, list[str]]
) -> list[str]:
    """
    Finds the directories that act as import paths in a repository: those under
    which some file sits at exactly the name some file imports it by.

    Args:
        proto_files: Paths of the .proto files, relative to the repository.
        imports: Imported names per file, from read_proto_imports.

    Returns:
        The roots, deepest first, always including the repository root as the
        fallback for files no import names.
    """
    imported = {name for names in imports.values() for name in names}
    roots = {REPO_ROOT}
    for file in proto_files:
        # Every way of splitting the path into a directory and a name, since
        # any of them could be the split some import wrote down.
        parts = file.split("/")
        for i in range(len(parts)):
            if "/".join(parts[i:]) in imported:
                roots.add("/".join(parts[:i]) or REPO_ROOT)
    return sorted(roots, key=lambda root: (-len(root), root))


def group_by_import_root(
    proto_files: list[str], imports: dict[str, list[str]], roots: list[str]
) -> dict[str, list[str]]:
    """
    Assigns each file the root to compile it under, and groups the files by it.

    A file under several roots is compiled under the one resolving the most of
    its own imports; ties go to the root that gives it the name other files
    import it by, and then to the deepest.

    Args:
        proto_files: Paths of the .proto files, relative to the repository.
        imports: Imported names per file, from read_proto_imports.
        roots: Candidate roots, from discover_import_roots.

    Returns:
        The files of each group, keyed by the root it is compiled under.
    """
    known = set(proto_files)
    imported = {name for names in imports.values() for name in names}
    candidates = set(roots)

    groups: dict[str, list[str]] = {}
    for file in proto_files:
        parts = file.split("/")
        best, best_score = REPO_ROOT, None
        for i in range(len(parts)):
            root = "/".join(parts[:i]) or REPO_ROOT
            if root not in candidates:
                continue
            prefix = "" if root == REPO_ROOT else root + "/"
            resolved = sum(
                1
                for name in imports[file]
                if name.startswith(WELL_KNOWN_PREFIX) or prefix + name in known
            )
            score = (resolved, file[len(prefix) :] in imported, len(prefix))
            if best_score is None or score > best_score:
                best, best_score = root, score
        groups.setdefault(best, []).append(file)
    return groups


def import_path_order(root: str, roots: list[str]) -> list[str]:
    """
    Orders the import paths for compiling the files of one group.

    The compiler resolves a name against the import paths in order, so the order
    decides which of several files of the same name a repository holds is the
    one an import means. The group's own root leads, so that its files win any
    contest over a name, and the rest follow by how much of their path they
    share with it: a workspace where a/a.proto imports "b.proto" means the
    b/b.proto beside it, not one of the fifty others in the repository.

    Args:
        root: The root the group is compiled under.
        roots: Every root of the repository, from discover_import_roots.

    Returns:
        All of the roots, the group's own first.
    """

    def shared(other: str) -> int:
        parts, others = root.split("/"), other.split("/")
        common = 0
        for a, b in zip(parts, others):
            if a != b:
                break
            common += 1
        return common

    rest = [r for r in roots if r != root]
    rest.sort(key=lambda other: (-shared(other), -len(other), other))
    return [root] + rest


def collect_proto_stats(
    pollux_bin: str, proto_files: list[str], log_error
) -> dict[str, dict]:
    """
    Runs `pollux proto stats` over a whole repository, from its root.

    One invocation per group of files rather than one per file: the compiler
    parses a shared import once instead of once per file that imports it, which
    is the difference between minutes and seconds on a repository the size of
    googleapis. Every root is passed as an import path so that a file importing
    across module boundaries still resolves, ordered by import_path_order.

    Args:
        pollux_bin: Path to the pollux binary.
        proto_files: Paths of the .proto files, relative to the repository.
        log_error: Called with one line per file that produced no statistics.

    Returns:
        The statistics of each file that compiled, keyed by the path given here.
    """
    imports = read_proto_imports(proto_files)
    roots = discover_import_roots(proto_files, imports)
    groups = group_by_import_root(proto_files, imports, roots)
    print(f"Compiling {len(proto_files)} file(s) in {len(groups)} group(s)")

    stats: dict[str, dict] = {}
    with Progress() as progress:
        task = progress.add_task("[green]Compiling proto files...", total=len(groups))

        for root in sorted(groups):
            command = [pollux_bin, "proto", "stats"]
            for path in import_path_order(root, roots):
                command += ["-I", path]
            command += groups[root]

            result = subprocess.run(command, capture_output=True, text=True)
            for line in result.stderr.splitlines():
                if line.strip():
                    log_error(line)
            if result.stdout.strip():
                try:
                    stats.update(json.loads(result.stdout))
                except json.JSONDecodeError as e:
                    log_error(f"unreadable statistics for the files under {root}: {e}")

            progress.update(task, advance=1)

    return stats


def _process_proto_repo_for_stats(
    owner: str,
    repo: str,
    repo_path: str,
    output_filename: str,
    error_log: str | None = None,
) -> None:
    """
    Helper function to process a git repository and extract proto file statistics.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        repo_path: Path to the cloned repository.
        output_filename: Path to save the parquet file.
        error_log: Optional path to log errors to disk.
    """
    pollux_bin = locate_pollux()

    original_cwd = os.getcwd()

    # Both are read after the working directory has moved into the repository.
    output_filename = os.path.abspath(output_filename)
    if error_log:
        error_log = os.path.abspath(error_log)

    os.chdir(repo_path)

    try:
        print("Finding .proto files...")
        result = subprocess.run(
            ["find", ".", "-name", "*.proto", "-type", "f"],
            capture_output=True,
            text=True,
            check=True,
        )
        # find prints "./a/b.proto"; only that prefix comes off, since
        # stripping the characters would rename a file under a dotted
        # directory into one the compiler cannot find.
        proto_files = [
            f.strip().removeprefix("./")
            for f in result.stdout.strip().split("\n")
            if f.strip()
        ]
        nproto = len(proto_files)
        print(f"Found {nproto} proto files in {owner}/{repo}")

        if nproto == 0:
            print(f"Nothing to record for {owner}/{repo}", file=sys.stderr)
            # A repository can lose its .proto files, and an output left
            # over from when it had some keeps that repository in the
            # dataset with whichever columns existed back then. Combining
            # parquet files keeps only the columns they all share, so one
            # stale file drops a counter from every plot.
            if os.path.exists(output_filename):
                os.remove(output_filename)
                print(f"Removed stale {output_filename}", file=sys.stderr)
            return

        error_log_file = None
        if error_log:
            try:
                error_log_file = open(error_log, "a")
            except IOError as log_err:
                print(f"Failed to open error log file: {log_err}", file=sys.stderr)
                error_log_file = None

        def log_error(message: str) -> None:
            print(f"[{owner}/{repo}] {message}", file=sys.stderr)
            if error_log_file:
                try:
                    error_log_file.write(f"[{owner}/{repo}] {message}\n")
                    error_log_file.flush()
                except IOError as log_err:
                    print(f"Failed to write to error log: {log_err}", file=sys.stderr)

        stats = {}
        if pollux_bin:
            stats = collect_proto_stats(pollux_bin, proto_files, log_error)
            print(f"Collected statistics for {len(stats)} of {nproto} file(s)")
        else:
            # Worth saying loudly: the run still produces a Parquet file,
            # but one with none of the counters in it, and combining it
            # with the others drops those counters from all of them.
            print(
                f"No pollux on PATH: {owner}/{repo} gets commit history and "
                "no statistics",
                file=sys.stderr,
            )

        data_rows = []

        with Progress() as progress:
            task = progress.add_task("[green]Reading commit history...", total=nproto)

            for file in proto_files:
                try:
                    result = subprocess.run(
                        ["git", "log", "--format=%H", "--", file],
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    commit_hashes = [
                        h.strip()
                        for h in result.stdout.strip().split("\n")
                        if h.strip()
                    ]
                except subprocess.CalledProcessError as e:
                    log_error(f"{file}: cannot read the commit history: {e}")
                    commit_hashes = []

                data_rows.append(
                    {
                        "repository": f"{owner}/{repo}",
                        "proto_file": file,
                        "commits": commit_hashes,
                        "commit_count": len(commit_hashes),
                        **stats.get(file, {}),
                    }
                )

                progress.update(task, advance=1)

        if error_log_file:
            try:
                error_log_file.close()
            except IOError:
                pass

    finally:
        os.chdir(original_cwd)

    # Files that did not compile carry no counters, so the rows are not all
    # shaped alike and the schema has to be read off all of them rather than
    # off the first few.
    df = pl.DataFrame(data_rows, infer_schema_length=None)

    # A repository whose every file failed to compile has no counters to
    # judge usefulness by, and nothing in it is useful.
    counted = [c for c in ("field_count_total", "enum_count_total") if c in df.columns]
    useful = pl.col("commits").list.len().gt(pl.lit(1))
    if counted:
        nonempty = pl.col(counted[0]).gt(pl.lit(0))
        for column in counted[1:]:
            nonempty = nonempty | pl.col(column).gt(pl.lit(0))
        useful = useful & nonempty
    else:
        useful = pl.lit(False)

    df = df.with_columns(
        useful=pl.when(useful).then(pl.lit(True)).otherwise(pl.lit(False))
    )

    df.write_parquet(output_filename)
    print(f"\n\nSaved commit history to {output_filename}")


def handle_fetch_command(args):
    """
    Main entry point for the fetch subcommand.

    Args:
        args: Parsed command-line arguments.
    """

    cache_dir = args.cache if hasattr(args, "cache") else None
    error_log = args.error_log if hasattr(args, "error_log") else None

    if args.search_go_repos:
        token = os.getenv("GITHUB_TOKEN")
        if token is None:
            raise ValueError("GITHUB_TOKEN environment variable is not set")
        repos = search_popular_go_repositories(token)
        print(f"Found {len(repos)} repositories")

        with Progress() as progress:
            task = progress.add_task(
                "[green]Processing Go repositories...", total=len(repos)
            )

            for r in repos:
                try:
                    time.sleep(7)  # Sleep to avoid rate limiting
                    if args.output is not None:
                        output_filename = os.path.join(
                            args.output, f"{r['owner']}-{r['name']}.parquet"
                        )
                    else:
                        output_filename = f"{r['owner']}-{r['name']}.parquet"

                    get_json_usage_parquet(
                        r["owner"], r["name"], token, output_filename
                    )
                except Exception as e:
                    print(f"Error processing {r['owner']}/{r['name']}: {e}")
                finally:
                    progress.update(task, advance=1)

        return

    if args.json_usage:
        token = os.getenv("GITHUB_TOKEN")
        if token is None:
            raise ValueError("GITHUB_TOKEN environment variable is not set")

        if args.all:
            fetch_repos = JSON_REPOS
        else:
            fetch_repos = [(args.repo[0], args.repo[1])]

        with Progress() as progress:
            task = progress.add_task(
                "[green]Processing Go repositories...", total=len(fetch_repos)
            )
            for r in fetch_repos:
                if args.output is None:
                    output_file = f"{r[0]}-{r[1]}.parquet"
                else:
                    output_file = os.path.join(args.output, f"{r[0]}-{r[1]}.parquet")

                try:
                    if args.api:
                        get_json_usage_parquet(r[0], r[1], token, output_file)
                    else:
                        if cache_dir:
                            print(
                                f"Using local cloning method with cache directory: {cache_dir}"
                            )
                        else:
                            print("Using local cloning method to temporary directory.")
                        get_json_usage_parquet_local(r[0], r[1], output_file, cache_dir)
                except Exception as e:
                    print(f"Error processing {r[0]}/{r[1]}: {e}")
                finally:
                    progress.update(task, advance=1)
        return

    if args.all:
        print("Fetch all repos")
        fetch_repos = PROTO_REPOS
    else:
        fetch_repos = [(args.repo[0], args.repo[1])]

    for r in fetch_repos:
        if args.output is None:
            output_file = f"{r[0]}-{r[1]}.parquet"
        else:
            output_file = os.path.join(args.output, f"{r[0]}-{r[1]}.parquet")

        # One repository that cannot be processed should not take the rest of
        # the dataset with it: the ones after it in the list would otherwise
        # keep whatever an earlier run left behind, and combining parquet files
        # keeps only the columns they all share.
        try:
            if args.api:
                print("Using GitHub API method (limited to 1000 proto files)")
                token = os.getenv("GITHUB_TOKEN")
                if token is None:
                    raise ValueError("GITHUB_TOKEN environment variable is not set")
                get_proto_history_parquet(r[0], r[1], token, output_file)
            else:
                if cache_dir:
                    print(
                        f"Using local cloning method with cache directory: {cache_dir}"
                    )
                else:
                    print("Using local cloning method (no API limits, requires git)")
                get_proto_history_parquet_local(
                    r[0], r[1], output_file, cache_dir, error_log
                )
        except Exception as e:
            print(f"Error processing {r[0]}/{r[1]}: {e}", file=sys.stderr)
