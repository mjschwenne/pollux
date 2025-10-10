import requests
import json
import time
import argparse
from rich.progress import Progress
from rich.pretty import pprint
import altair as alt
import pandas as pd
import numpy as np

import os
import tempfile
import subprocess


def locate_pollux() -> str:
    try:
        w = subprocess.run(
            ["which", "pollux"],
            check=True,
            capture_output=True,
            text=True,
        )
        return w.stdout.strip()
    except subprocess.CalledProcessError as e:
        print(f"Error finding pollux binary: {e}")

    return ""


def paginated_github_query(
    url: str, headers: dict[str, str], per_page: int = 100
) -> list[dict[str, str]]:
    """
    Generic function to handle paginated GitHub API queries.
    Limited to 1000 total results by GitHub Search API.

    Args:
        url: Base URL for the GitHub API endpoint.
        headers: Headers to include in the request.
        per_page: Number of items to fetch per page.

    Returns:
        List of all items from all pages (max 1000 items).
    """
    page = 1

    paginated_url = f"{url}&per_page={per_page}&page={page}"
    response = requests.get(paginated_url, headers=headers)
    response.raise_for_status()
    all_items = [response.json()]

    while "next" in response.links:
        page += 1
        time.sleep(6)  # Sleep to avoid rate limiting of 10 requests per minute

        paginated_url = f"{url}&per_page={per_page}&page={page}"
        response = requests.get(paginated_url, headers=headers)
        response.raise_for_status()
        items = response.json()

        all_items.append(items)

    return all_items


def get_proto_history_json(
    owner: str, repo: str, github_token: str, output_filename: str
) -> None:
    """
    Fetches the commit history for all .proto files in a GitHub repository
    using the GitHub API and saves the result as a JSON file.

    Limited to 1000 proto files due to GitHub Search API constraints.
    Use get_proto_history_json_local() for larger repositories.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        github_token: GitHub personal access token for authentication.
    """
    # Step 1: Search for .proto files using pagination
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

    # Initialize JSON output
    json_output: dict[str, list[str]] = {}

    # Step 2: Fetch commit history for each .proto file
    with Progress() as progress:
        task = progress.add_task("[green]Processing proto files...", total=nproto)

        for file in proto_files:
            commits_url = (
                f"https://api.github.com/repos/{owner}/{repo}/commits?path={file}"
            )
            results = paginated_github_query(commits_url, headers)
            commit_hashes = [commits["sha"] for page in results for commits in page]
            json_output[file] = commit_hashes

            progress.update(task, advance=1)
            time.sleep(1)  # Avoid rate limiting

    # Step 3: Save JSON output
    with open(output_filename, "w") as f:
        json.dump(json_output, f, indent=2)
        _ = f.write("\n")
    print(f"\n\nSaved commit history to {output_filename}")


def get_proto_history_json_local(owner: str, repo: str, output_filename: str) -> None:
    """
    Clones a repository locally to extract commit history for all .proto files.
    This bypasses GitHub API limits for large repositories.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
    """
    # Create temporary directory
    with tempfile.TemporaryDirectory() as temp_dir:
        repo_url = f"https://github.com/{owner}/{repo}.git"
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

        pollux_bin = locate_pollux()

        # Change to repo directory
        original_cwd = os.getcwd()
        os.chdir(repo_path)

        try:
            # Find all .proto files
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

            # Initialize JSON output
            json_output: dict[str, list[str]] = {}

            # Get commit history for each .proto file
            with Progress() as progress:
                task = progress.add_task(
                    "[green]Processing proto files...", total=nproto
                )

                for file in proto_files:
                    try:
                        # Get commit hashes for this file
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
                        # Get stats file
                        stats_json = subprocess.run(
                            [pollux_bin, "stats", file],
                            capture_output=True,
                            text=True,
                            check=True,
                        )
                        stats = json.loads(stats_json.stdout)
                        json_output[file] = {"commits": commit_hashes, **stats[file]}
                    except subprocess.CalledProcessError:
                        # If git log fails for a file, set empty list
                        json_output[file] = []

                    progress.update(task, advance=1)

        finally:
            # Return to original directory
            os.chdir(original_cwd)

        # Save JSON output
        with open(output_filename, "w") as f:
            json.dump(json_output, f, indent=2)
            _ = f.write("\n")
        print(f"\n\nSaved commit history to {output_filename}")


def plot_commit_histogram(
    json_files: list[str], output_file: str | None = None
) -> alt.Chart | alt.LayerChart:
    """
    Creates a histogram showing the distribution of commits per proto file.

    Args:
        json_files: List of paths to JSON files output by get_proto_history_json
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """
    all_commit_counts = []
    all_data = []

    # Load and combine data from all JSON files
    for json_file in json_files:
        with open(json_file, "r") as f:
            data = json.load(f)

        # Extract repository name from filename
        repo_name = os.path.basename(json_file).replace(".json", "")

        # Count commits per file and store with repository info
        for proto_file, commits in data.items():
            commit_count = len(commits)
            all_commit_counts.append(commit_count)
            all_data.append(
                {
                    "proto_file": proto_file,
                    "commit_count": commit_count,
                    "repository": repo_name,
                }
            )

    # Calculate statistics
    mean_commits = np.mean(all_commit_counts)
    total_files = len(all_commit_counts)
    total_repos = len(json_files)

    # Create DataFrame for Altair
    df = pd.DataFrame(all_data)

    # Create base chart
    base = alt.Chart(df)

    # Create histogram with explicit integer bins
    min_commits = min(all_commit_counts)
    max_commits = max(all_commit_counts)

    histogram = (
        base.mark_bar(opacity=0.7, color="steelblue")
        .encode(
            alt.X(
                "commit_count:Q",
                bin=alt.Bin(extent=[min_commits - 0.5, max_commits + 0.5], step=1),
                title="Number of Commits per Proto File",
                axis=alt.Axis(tickMinStep=1, format=".0f"),
            ),
            alt.Y("count()", title="Number of Proto Files"),
            tooltip=["count()", "commit_count:Q"],
        )
        .properties(
            width=600,
            height=400,
            title=f"Combined Distribution of Commits per Proto File\n{total_files} files from {total_repos} repositories (Mean: {mean_commits:.2f})",
        )
    )

    # Create vertical line for mean with legend
    mean_line = (
        alt.Chart(pd.DataFrame({"mean": [mean_commits], "legend": ["Mean"]}))
        .mark_rule(color="red", strokeWidth=2, strokeDash=[5, 5])
        .encode(
            x=alt.X("mean:Q", axis=alt.Axis(tickMinStep=1)),
            color=alt.Color(
                "legend:N",
                scale=alt.Scale(range=["red"]),
                legend=alt.Legend(title="Statistics"),
            ),
        )
    )

    # Combine histogram and mean line
    chart = histogram + mean_line

    # Save or display
    if output_file:
        # Determine format from file extension
        if output_file.endswith(".png"):
            chart.save(output_file, scale_factor=2.0)
            print(f"Plot saved to {output_file}")
        elif output_file.endswith(".html") or "." not in output_file:
            # Default to HTML if no extension or explicit .html
            if "." not in output_file:
                output_file += ".html"
            chart.save(output_file)
            print(f"Plot saved to {output_file}")
        else:
            # Try to save with whatever extension was provided
            chart.save(output_file)
            print(f"Plot saved to {output_file}")
    else:
        chart.show()

    return chart


def main():
    parser = argparse.ArgumentParser(
        description="Fetch commit history for .proto files in a GitHub repository or visualize existing data",
        epilog="""
Examples:
  # Fetch using GitHub API (fast, limited to 1000 files)
  python eval.py fetch googleapis google-cloud-go

  # Fetch using local cloning (no limits, slower)
  python eval.py fetch googleapis googleapis --local

  # Compare both methods
  python eval.py compare mjschwenne grackle

  # Create visualizations from single file
  python eval.py visualize data.json --type histogram --output plot.png

  # Create combined visualizations from multiple files
  python eval.py visualize --type histogram mjschwenne-grackle.json googleapis-googleapis.json --output combined-histogram.png

Note: GitHub API method requires GITHUB_TOKEN environment variable.
      Local method requires git but no token.
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    # Create subparsers for different commands
    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Subparser for fetching data
    _ = fetch_parser = subparsers.add_parser(
        "fetch", help="Fetch commit history from GitHub"
    )
    _ = fetch_parser.add_argument("owner", help="GitHub repository owner/username")
    _ = fetch_parser.add_argument("repo", help="GitHub repository name")
    _ = fetch_parser.add_argument(
        "--local",
        action="store_true",
        help="Clone repository locally to bypass API limits. Use this for large repos with >1000 proto files or extensive commit histories. Requires git but no GitHub token.",
    )
    _ = fetch_parser.add_argument(
        "--output",
        help="Path to output the JSON summary. Defaults to <owner>-<repo>.json",
    )

    # Subparser for comparing methods
    compare_parser = subparsers.add_parser(
        "compare", help="Compare GitHub API and local cloning methods"
    )
    _ = compare_parser.add_argument("owner", help="GitHub repository owner/username")
    _ = compare_parser.add_argument("repo", help="GitHub repository name")

    # Subparser for visualization
    viz_parser = subparsers.add_parser(
        "visualize", help="Create visualizations from JSON data"
    )
    _ = viz_parser.add_argument(
        "json_files",
        nargs="+",
        help="Path(s) to JSON file(s) created by get_proto_history_json",
    )
    _ = viz_parser.add_argument(
        "--type",
        choices=["histogram"],
        default="histogram",
        help="Type of plot to create (default: histogram)",
    )
    _ = viz_parser.add_argument(
        "--output",
        help="Output file path for saving the plot (format determined by file extension: .png, .html, etc.)",
    )
    _ = viz_parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed statistics about the data",
    )

    args = parser.parse_args()

    if args.command == "fetch":
        if args.output is None:
            args.output = f"{args.owner}-{args.repo}.json"
        if args.local:
            # Use local cloning method - no API limits
            print("Using local cloning method (no API limits, requires git)")
            get_proto_history_json_local(args.owner, args.repo, args.output)
        else:
            # Use GitHub API method - limited to 1000 results
            print("Using GitHub API method (limited to 1000 proto files)")
            token = os.getenv("GITHUB_TOKEN")
            if token is None:
                raise ValueError("GITHUB_TOKEN environment variable is not set")
            get_proto_history_json(args.owner, args.repo, token, args.output)

    elif args.command == "compare":
        token = os.getenv("GITHUB_TOKEN")
        if token is None:
            raise ValueError("GITHUB_TOKEN environment variable is not set")
        success = compare_methods(args.owner, args.repo, token)
        if success:
            print("✅ Both methods produced consistent results")
        else:
            print("❌ Methods produced inconsistent results")

    elif args.command == "visualize":
        # Load and analyze data if verbose mode is requested
        if args.verbose:
            print("Creating visualizations from proto commit history...")
            print(f"Using data from: {', '.join(args.json_files)}")

            # Load and examine all data files
            all_commit_counts = []
            all_file_commit_pairs = []
            total_files = 0
            total_commits = 0

            for json_file in args.json_files:
                with open(json_file, "r") as f:
                    data = json.load(f)

                repo_name = os.path.basename(json_file).replace(".json", "")
                commit_counts = [len(commits) for commits in data.values()]
                all_commit_counts.extend(commit_counts)

                # Track per-repository stats
                repo_total_files = len(data)
                repo_total_commits = sum(commit_counts)
                total_files += repo_total_files
                total_commits += repo_total_commits

                print(f"\n{repo_name} Summary:")
                print(f"  Proto files: {repo_total_files}")
                print(f"  Total commits: {repo_total_commits}")
                print(f"  Average commits per file: {np.mean(commit_counts):.2f}")

                # Collect file-commit pairs for global ranking
                for file, commits in data.items():
                    all_file_commit_pairs.append((f"{repo_name}:{file}", len(commits)))

            # Print combined statistics
            print(f"\nCombined Data Summary:")
            print(f"  Total repositories: {len(args.json_files)}")
            print(f"  Total proto files: {total_files}")
            print(f"  Total commits: {total_commits}")
            print(f"  Average commits per file: {np.mean(all_commit_counts):.2f}")
            print(f"  Min commits per file: {min(all_commit_counts)}")
            print(f"  Max commits per file: {max(all_commit_counts)}")
            print(f"  Standard deviation: {np.std(all_commit_counts):.2f}")

            # Show top files across all repositories
            all_file_commit_pairs.sort(key=lambda x: x[1], reverse=True)
            print(f"\nTop files by commit count (across all repositories):")
            for i, (file, count) in enumerate(all_file_commit_pairs[:5]):
                print(f"  {i+1}. {file}: {count} commits")
            print()

        # Create the requested visualization
        if args.type == "histogram":
            if args.verbose:
                print("Creating combined histogram plot...")
            plot_commit_histogram(args.json_files, args.output)

        if args.verbose:
            print("\nVisualization complete!")

    else:
        parser.print_help()


def compare_methods(owner: str, repo: str, github_token: str) -> bool:
    """
    Compare results from both GitHub API and local cloning methods.
    Returns True if results are consistent, False otherwise.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        github_token: GitHub personal access token for authentication.

    Returns:
        bool: True if methods produce consistent results.
    """
    print(f"Comparing methods for {owner}/{repo}")

    # Save original files with temporary names
    api_file = f"{owner}-{repo}-api.json"
    local_file = f"{owner}-{repo}-local.json"

    try:
        # Get results from GitHub API
        print("Fetching via GitHub API...")
        get_proto_history_json(owner, repo, github_token, api_file)
        os.rename(f"{owner}-{repo}.json", api_file)

        # Get results from local cloning
        print("Fetching via local cloning...")
        get_proto_history_json_local(owner, repo, local_file)
        os.rename(f"{owner}-{repo}.json", local_file)

        # Load both results
        with open(api_file, "r") as f:
            api_data = json.load(f)
        with open(local_file, "r") as f:
            local_data = json.load(f)

        # Compare results
        api_files = set(api_data.keys())
        local_files = set(local_data.keys())

        print(f"API method found: {len(api_files)} files")
        print(f"Local method found: {len(local_files)} files")

        # Check if local method found more files (expected for large repos)
        if len(local_files) > len(api_files):
            print("Local method found more files (expected for large repos)")

        # Check consistency for files found by both methods
        common_files = api_files.intersection(local_files)
        print(f"Files found by both methods: {len(common_files)}")

        inconsistent_files = []
        for file in common_files:
            api_commits = set(api_data[file])
            local_commits = set(local_data[file])
            if api_commits != local_commits:
                inconsistent_files.append(file)
                print(f"Inconsistent commits for {file}:")
                print(f"  API: {len(api_commits)} commits")
                print(f"  Local: {len(local_commits)} commits")

        if inconsistent_files:
            print(f"Found {len(inconsistent_files)} files with inconsistent results")
            return False
        else:
            print("All common files have consistent commit histories")
            return True

    finally:
        # Clean up temporary files
        for temp_file in [api_file, local_file]:
            if os.path.exists(temp_file):
                os.remove(temp_file)


if __name__ == "__main__":
    main()
