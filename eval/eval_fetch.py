import requests
import time
import os
import sys
import tempfile
import subprocess
import json
from rich.progress import Progress
import polars as pl

# Handle imports for both script and package usage
try:
    from .eval_utils import PROTO_REPOS, locate_pollux, paginated_github_query
except ImportError:
    from eval_utils import PROTO_REPOS, locate_pollux, paginated_github_query


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

        _process_repo_for_stats(owner, repo, repo_path, output_filename, error_log)
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

            _process_repo_for_stats(owner, repo, repo_path, output_filename, error_log)


def _process_repo_for_stats(
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
        proto_files = [
            f.strip().lstrip("./")
            for f in result.stdout.strip().split("\n")
            if f.strip()
        ]
        nproto = len(proto_files)
        print(f"Found {nproto} proto files in {owner}/{repo}")

        data_rows = []

        error_log_file = None
        if error_log:
            try:
                error_log_file = open(error_log, "a")
            except IOError as log_err:
                print(f"Failed to open error log file: {log_err}", file=sys.stderr)
                error_log_file = None

        with Progress() as progress:
            task = progress.add_task("[green]Processing proto files...", total=nproto)

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

                    row_data = {
                        "repository": f"{owner}/{repo}",
                        "proto_file": file,
                        "commits": commit_hashes,
                        "commit_count": len(commit_hashes),
                    }

                    if pollux_bin:
                        try:
                            stats_json = subprocess.run(
                                [pollux_bin, "stats", file],
                                capture_output=True,
                                text=True,
                                check=True,
                            )
                            stats = json.loads(stats_json.stdout)
                            if file in stats:
                                row_data.update(stats[file])
                        except subprocess.CalledProcessError as e:
                            print(
                                f"[{owner}/{repo}] Error in file: {file}",
                                file=sys.stderr,
                            )
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
                            error_msg = f"[{owner}/{repo}] Error parsing pollux stats output for {file}: {e}"
                            print(error_msg, file=sys.stderr)
                            if error_log_file:
                                try:
                                    error_log_file.write(f"{error_msg}\n")
                                    error_log_file.flush()
                                except IOError:
                                    pass

                    data_rows.append(row_data)

                except subprocess.CalledProcessError as e:
                    print(e)
                    data_rows.append(
                        {
                            "repository": f"{owner}/{repo}",
                            "proto_file": file,
                            "commits": [],
                            "commit_count": 0,
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

    df = pl.DataFrame(data_rows)

    df = df.with_columns(
        useful=pl.when(
            pl.col("commits").list.len().gt(pl.lit(1))
            & (
                pl.col("field_count_total").gt(pl.lit(0))
                | pl.col("enum_count_total").gt(pl.lit(0))
            )
        )
        .then(pl.lit(True))
        .otherwise(pl.lit(False))
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

        if args.api:
            print("Using GitHub API method (limited to 1000 proto files)")
            token = os.getenv("GITHUB_TOKEN")
            if token is None:
                raise ValueError("GITHUB_TOKEN environment variable is not set")
            get_proto_history_parquet(r[0], r[1], token, output_file)
        elif args.json_usage:
            token = os.getenv("GITHUB_TOKEN")
            if token is None:
                raise ValueError("GITHUB_TOKEN environment variable is not set")
            get_json_usage_parquet(r[0], r[1], token, output_file)
        else:
            if cache_dir:
                print(f"Using local cloning method with cache directory: {cache_dir}")
            else:
                print("Using local cloning method (no API limits, requires git)")
            get_proto_history_parquet_local(
                r[0], r[1], output_file, cache_dir, error_log
            )
