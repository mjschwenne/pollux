import requests
import time
import argparse
from rich.progress import Progress
import altair as alt
import polars as pl

import os
import tempfile
import subprocess
import json

REPOS = [
    ("googleapis", "googleapis"),
    ("googleapis", "google-cloud-go"),
    ("colinmarc", "hdfs"),
    ("protocolbuffers", "protobuf"),
    ("google", "protobuf.dart"),
    ("bufbuild", "buf"),
    ("go-kratos", "kratos"),
    ("cloudwego", "kitex"),
    ("twitchtv", "twirp"),
    ("asynkron", "protoactor-go"),
    ("samchon", "typia"),
    ("uber", "prototool"),
    ("streamdal", "plumber"),
    ("google", "rejoiner"),
]


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

    # Initialize data for DataFrame
    data_rows = []

    # Step 2: Fetch commit history for each .proto file
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

    # Step 3: Create DataFrame and save as Parquet
    df = pl.DataFrame(data_rows)
    df.write_parquet(output_filename)
    print(f"\n\nSaved commit history to {output_filename}")


def get_proto_history_parquet_local(
    owner: str, repo: str, output_filename: str, cache_dir: str | None = None
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
    """
    repo_url = f"https://github.com/{owner}/{repo}.git"
    repo_name = f"{owner}-{repo}"

    # Determine if we should use cache or temporary directory
    if cache_dir:
        # Use cache directory
        os.makedirs(cache_dir, exist_ok=True)
        repo_path = os.path.join(cache_dir, repo_name)

        if os.path.exists(repo_path):
            print(f"Using cached repository at {repo_path}")
            # Update the repository to ensure it's current
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

        # Process the cached repository
        _process_repo_for_stats(owner, repo, repo_path, output_filename)
    else:
        # Use temporary directory (original behavior)
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

            _process_repo_for_stats(owner, repo, repo_path, output_filename)


def _process_repo_for_stats(
    owner: str, repo: str, repo_path: str, output_filename: str
) -> None:
    """
    Helper function to process a git repository and extract proto file statistics.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        repo_path: Path to the cloned repository.
        output_filename: Path to save the parquet file.
    """
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

            # Initialize data for DataFrame
            data_rows = []

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

                        # Initialize row data
                        row_data = {
                            "repository": f"{owner}/{repo}",
                            "proto_file": file,
                            "commits": commit_hashes,
                            "commit_count": len(commit_hashes),
                        }

                        # Get stats file if pollux is available
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
                                    # Add pollux stats to row data
                                    row_data.update(stats[file])
                            except (
                                subprocess.CalledProcessError,
                                json.JSONDecodeError,
                                KeyError,
                            ) as e:
                                # If pollux stats fail, continue without them
                                print(e)
                                pass

                        data_rows.append(row_data)

                    except subprocess.CalledProcessError as e:
                        # If git log fails for a file, add empty entry
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

    finally:
        # Return to original directory
        os.chdir(original_cwd)

    # Create DataFrame and save as Parquet
    df = pl.DataFrame(data_rows)
    df.write_parquet(output_filename)
    print(f"\n\nSaved commit history to {output_filename}")


def load_parquet_data(parquet_files: list[str]) -> pl.DataFrame:
    """
    Loads and combines data from multiple parquet files.

    Args:
        parquet_files: List of paths to parquet files.

    Returns:
        Combined polars DataFrame
    """
    if len(parquet_files) == 1:
        return pl.read_parquet(parquet_files[0])
    else:
        # Read and combine multiple files, handling schema differences
        dfs = [pl.read_parquet(file) for file in parquet_files]

        # Find common columns across all DataFrames
        common_cols = set(dfs[0].columns)
        for df in dfs[1:]:
            common_cols &= set(df.columns)

        # Select only common columns from each DataFrame
        aligned_dfs = [df.select(sorted(common_cols)) for df in dfs]

        return pl.concat(aligned_dfs)


def save_plot(chart: alt.Chart | alt.LayerChart, output_file: str | None = None):
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
        # If no output file specified, save as default HTML file
        # This avoids the IPython dependency issue with chart.show()
        output_file = "plot.html"
        chart.save(output_file)
        print(f"No output file specified, saved plot to {output_file}")


def plot_commit_histogram(
    df: pl.DataFrame, output_file: str | None = None
) -> alt.Chart | alt.LayerChart:
    """
    Creates a histogram showing the distribution of commits per proto file.

    Args:
        parquet_files: List of paths to parquet files.
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """
    # Calculate statistics
    mean_commits = df["commit_count"].mean()
    total_files = len(df)
    total_repos = df["repository"].n_unique()

    # Create base chart - use the dataframe directly
    base = alt.Chart(df)

    histogram = (
        base.mark_bar(color="steelblue")
        .encode(
            alt.X(
                "commit_count:Q",
                bin=alt.Bin(maxbins=20, minstep=1),
                title="Number of Commits per Proto File",
                axis=alt.Axis(tickMinStep=1, format=".0f"),
            ),
            alt.Y("count()", title="Number of Proto Files"),
            tooltip=["count()", "commit_count:Q"],
        )
        .properties(
            width=600,
            height=400,
            title=[
                f"Distribution of Commits per Proto File",
                f"{total_files} files from {total_repos} repositories (Mean: {mean_commits:.2f})",
            ],
        )
    )

    # Create vertical line for mean with legend
    mean_df = pl.DataFrame({"mean": [mean_commits], "legend": ["Mean"]})
    mean_line = (
        alt.Chart(mean_df)
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
    save_plot(chart, output_file)

    return chart


def plot_histogram(
    df: pl.DataFrame, attr: str, attr_name: str, output_file: str | None = None
) -> alt.Chart | alt.LayerChart:
    """
    Creates a histogram showing the distribution the given dataframe attribute.

    Args:
        df: Loaded data frame
        attr: The column name in df to plot
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """

    if attr not in df.columns:
        raise ValueError(
            f"'{attr}' columns not found in data. Exclude the --api flag when fetching to get full stats."
        )

    mean = df[attr].mean()

    base = alt.Chart(df)
    alt_attr = f"{attr}:Q"

    histogram = (
        base.mark_bar(color="steelblue")
        .encode(
            alt.X(
                alt_attr,
                bin=alt.Bin(maxbins=20, minstep=1),
                title=f"Number of {attr_name} per Proto File",
                axis=alt.Axis(tickMinStep=1, format=".0f"),
            ),
            alt.Y("count()", title="Number of Proto Files"),
            tooltip=["count()", alt_attr],
        )
        .properties(
            width=600,
            height=400,
            title=[
                f"Distribution of {attr_name} per Proto File",
                f"{len(df)} files from {df['repository'].n_unique()} repositories (Mean: {mean:.2f})",
            ],
        )
    )

    mean_df = pl.DataFrame({"mean": [mean], "legend": ["Mean"]})
    mean_line = (
        alt.Chart(mean_df)
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
    save_plot(chart, output_file)

    return chart


def plot_proto_type_breakdown(
    df: pl.DataFrame, output_file: str | None = None
) -> alt.Chart:
    """
    Creates a mosaic plot showing the breakdown of protobuf types (messages, enums, services) by repository.

    Args:
        df: Polars DataFrame containing protobuf data with columns: repository, message_count_total, enum_count_total, service_count_total
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart object
    """
    # Required columns
    required_cols = [
        "repository",
        "message_count_total",
        "enum_count_total",
        "service_count_total",
    ]
    missing_cols = [col for col in required_cols if col not in df.columns]
    if missing_cols:
        raise ValueError(f"Missing required columns: {missing_cols}")

    # Aggregate data by repository
    repo_agg = df.group_by("repository").agg(
        [
            pl.col("message_count_total").sum().alias("Messages"),
            pl.col("enum_count_total").sum().alias("Enums"),
            pl.col("service_count_total").sum().alias("Services"),
        ]
    )

    # Calculate totals for each repository
    repo_agg = repo_agg.with_columns(
        (pl.col("Messages") + pl.col("Enums") + pl.col("Services")).alias("total")
    )

    # Filter out repositories with no protobuf elements
    repo_agg = repo_agg.filter(pl.col("total") > 0)

    # Sort by total count descending for better visualization
    repo_agg = repo_agg.sort("total", descending=True)

    # Limit to top 20 repositories if there are too many for readability
    if len(repo_agg) > 20:
        repo_agg = repo_agg.head(20)
        print(
            f"Note: Showing top 20 repositories out of {len(repo_agg)} total repositories"
        )

    # Create separate records for each type
    messages_df = repo_agg.select(
        [
            pl.col("repository"),
            pl.lit("Messages").alias("type"),
            pl.col("Messages").alias("count"),
            pl.col("total"),
        ]
    )

    enums_df = repo_agg.select(
        [
            pl.col("repository"),
            pl.lit("Enums").alias("type"),
            pl.col("Enums").alias("count"),
            pl.col("total"),
        ]
    )

    services_df = repo_agg.select(
        [
            pl.col("repository"),
            pl.lit("Services").alias("type"),
            pl.col("Services").alias("count"),
            pl.col("total"),
        ]
    )

    # Combine all type records
    plot_df = pl.concat([messages_df, enums_df, services_df])

    # Calculate percentages and positions for mosaic plot
    plot_df = plot_df.with_columns(
        (pl.col("count") / pl.col("total") * 100).alias("percentage")
    )

    # Calculate cumulative percentages for positioning
    plot_df_sorted = plot_df.sort(["repository", "type"])

    # Create position data for each segment
    position_data = []
    for repo in repo_agg["repository"]:
        repo_data = plot_df.filter(pl.col("repository") == repo)
        cumsum = 0
        for row in repo_data.iter_rows(named=True):
            y_start = cumsum
            y_end = cumsum + row["percentage"]
            position_data.append(
                {
                    "repository": repo,
                    "type": row["type"],
                    "count": row["count"],
                    "percentage": row["percentage"],
                    "y_start": y_start,
                    "y_end": y_end,
                    "y_mid": (y_start + y_end + 2) / 2,
                    "total": row["total"],
                    "label": [row["type"], str(row["count"])],
                }
            )
            cumsum += row["percentage"]

    mosaic_df = pl.DataFrame(position_data)

    # Create base mosaic chart with rectangles
    selection = alt.selection_point()
    base_chart = (
        alt.Chart(mosaic_df)
        .add_params(selection)
        .mark_rect(stroke="white", strokeWidth=2)
        .encode(
            x=alt.X(
                "repository:N",
                title="Repository",
                sort=alt.Sort(field="total", order="descending"),
                axis=alt.Axis(labelAngle=-45, labelLimit=200),
            ),
            y=alt.Y(
                "y_start:Q",
                scale=alt.Scale(domain=[0, 100]),
                title="Percentage of Protobuf Elements",
            ),
            y2=alt.Y2("y_end:Q"),
            color=alt.Color(
                "type:N",
                title="Element Type",
                scale=alt.Scale(
                    domain=["Messages", "Enums", "Services"],
                    range=["#1f77b4", "#ff7f0e", "#2ca02c"],
                ),
            ),
            tooltip=[
                alt.Tooltip("repository:N", title="Repository"),
                alt.Tooltip("type:N", title="Type"),
                alt.Tooltip("count:Q", title="Count"),
                alt.Tooltip("percentage:Q", title="Percentage", format=".1f"),
                alt.Tooltip("total:Q", title="Total Elements"),
            ],
        )
    )

    # Add text labels for each cell
    text_chart = (
        alt.Chart(mosaic_df)
        .mark_text(
            align="center",
            baseline="middle",
            fontSize=10,
            fontWeight="bold",
            color="white",
        )
        .encode(
            x=alt.X("repository:N", sort=alt.Sort(field="total", order="descending")),
            y=alt.Y("y_mid:Q", scale=alt.Scale(domain=[0, 100])),
            text=alt.condition(
                alt.datum.percentage > 4,  # Only show labels if segment is large enough
                alt.Text("label:N"),
                alt.value(""),
            ),
        )
    )

    # Combine charts
    chart = (
        (base_chart + text_chart)
        .properties(
            width=max(600, min(1200, len(repo_agg) * 80)),
            height=500,
            title=[
                "Protobuf Top LeveBreakdown by Repository",
                f'Showing {len(repo_agg)} repositories with {plot_df["total"].sum() // 3} total elements',
            ],
        )
        .resolve_scale(color="independent")
    )

    save_plot(chart, output_file)

    return chart


def plot_field_type_distribution(
    df: pl.DataFrame, output_file: str | None = None
) -> alt.Chart:
    """
    Creates a bar chart showing the distribution of field types across all proto files.
    Groups varint types (int64, int32, uint64, uint32, sint32, sint64) into a single "varints" category.

    Args:
        df: Polars DataFrame containing protobuf data with field_count_* columns
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart object
    """
    # Define field type columns to include (excluding total, implicit, optional, repeated)
    field_type_columns = [
        "field_count_double",
        "field_count_float",
        "field_count_int64",
        "field_count_uint64",
        "field_count_int32",
        "field_count_fixed64",
        "field_count_fixed32",
        "field_count_bool",
        "field_count_string",
        "field_count_message",
        "field_count_bytes",
        "field_count_uint32",
        "field_count_enum",
        "field_count_sfixed64",
        "field_count_sfixed32",
        "field_count_sint64",
        "field_count_sint32",
        "field_count_oneof",
    ]

    # Check that required columns exist
    missing_cols = [col for col in field_type_columns if col not in df.columns]
    if missing_cols:
        raise ValueError(
            f"Missing required columns: {missing_cols}. Exclude the --api flag when fetching to get full stats."
        )

    # Varint types to group together
    varint_columns = [
        "field_count_int64",
        "field_count_int32",
        "field_count_uint64",
        "field_count_uint32",
        "field_count_sint32",
        "field_count_sint64",
    ]

    # Calculate total counts for each field type across all files
    field_totals = {}

    # Sum varint types together
    varint_total = sum(df[col].sum() for col in varint_columns)
    field_totals["varints"] = varint_total

    # Sum other field types individually
    for col in field_type_columns:
        if col not in varint_columns:
            # Extract the type name from column name (e.g., "field_count_double" -> "double")
            type_name = col.replace("field_count_", "")
            field_totals[type_name] = df[col].sum()

    # Create DataFrame for plotting
    plot_data = pl.DataFrame(
        {"field_type": list(field_totals.keys()), "count": list(field_totals.values())}
    )

    # Filter out types with zero counts
    plot_data = plot_data.filter(pl.col("count") > 0)

    # Sort by count descending
    plot_data = plot_data.sort("count", descending=True)

    # Calculate total fields and percentages
    total_fields = plot_data["count"].sum()
    plot_data = plot_data.with_columns(
        (pl.col("count") / total_fields * 100).alias("percentage")
    )

    # Create bar chart
    chart = (
        alt.Chart(plot_data)
        .mark_bar(color="steelblue")
        .encode(
            x=alt.X(
                "field_type:N",
                title="Field Type",
                sort="-y",
                axis=alt.Axis(labelAngle=-45, labelLimit=150),
            ),
            y=alt.Y(
                "count:Q",
                title="Total Count Across All Proto Files",
            ),
            tooltip=[
                alt.Tooltip("field_type:N", title="Field Type"),
                alt.Tooltip("count:Q", title="Count", format=","),
                alt.Tooltip("percentage:Q", title="Percentage", format=".2f"),
            ],
        )
        .properties(
            width=600,
            height=400,
            title=[
                "Distribution of Protobuf Field Types",
                f"{total_fields:,} fields across {len(df)} files from {df['repository'].n_unique()} repositories",
                "(varint types grouped together)",
            ],
        )
    )

    save_plot(chart, output_file)

    return chart


def main():
    parser = argparse.ArgumentParser(
        description="Run evalutation tasks for the Pollux project.",
        epilog="""
Examples:
  # Fetch using GitHub API (fast, limited to 1000 files)
  python eval.py fetch --api googleapis google-cloud-go

  # Fetch using local cloning (no limits, slower)
  python eval.py fetch googleapis googleapis

  # Compare both methods
  python eval.py compare mjschwenne grackle

  # Create visualizations from single file
  python eval.py visualize data.parquet --type commits --output plot.png

  # Create combined visualizations from multiple files
  python eval.py visualize --type commits mjschwenne-grackle.parquet googleapis-googleapis.parquet --output combined-histogram.png

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
    ty = fetch_parser.add_mutually_exclusive_group(required=True)
    _ = ty.add_argument("--all", action="store_true", help="Fetch data from all repositories")
    _ = ty.add_argument("--repo", nargs=2, help="Fetch data from a specific repository")
    _ = fetch_parser.add_argument(
        "--api",
        action="store_true",
        help="Perform a limited analysis using the GitHub REST API. Doesn't download anything, but does require GITHUB_TOKEN env var to be set.",
    )
    _ = fetch_parser.add_argument(
        "--cache",
        type=str,
        help="Cache directory path. Repos will be cached as <owner>-<repo>. If not provided, uses temporary directory.",
    )
    _ = fetch_parser.add_argument(
        "--output",
        help="Path to output the Parquet file in. Each repo will be output as <owner>-<repo>.parquet",
    )

    # Subparser for comparing methods
    compare_parser = subparsers.add_parser(
        "compare", help="Compare GitHub API and local cloning methods"
    )
    _ = compare_parser.add_argument("owner", help="GitHub repository owner/username")
    _ = compare_parser.add_argument("repo", help="GitHub repository name")

    # Subparser for visualization
    viz_parser = subparsers.add_parser(
        "visualize", help="Create visualizations from Parquet data"
    )
    _ = viz_parser.add_argument(
        "parquet_files",
        nargs="+",
        help="Path(s) to Parquet file(s) created by fetch command",
    )
    _ = viz_parser.add_argument(
        "--type",
        choices=[
            "commits",
            "messages",
            "fields",
            "enums",
            "enum_vals",
            "services",
            "methods",
            "breakdown",
            "field_types",
        ],
        default="commits",
        help="Type of plot to create (default: commits)",
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
        print(f"{args=}")
        if args.all:
            print("Fetch all repos")
            fetch_repos = REPOS
        else:
            fetch_repos = [(args.repo[0], args.repo[1])]

        cache_dir = args.cache if hasattr(args, 'cache') else None

        for r in fetch_repos:
            if args.output is None:
                output_file = f"{r[0]}-{r[1]}.parquet"
            else:
                output_file = os.path.join(args.output, f"{r[0]}-{r[1]}.parquet")

            if args.api:
                # Use GitHub API method - limited to 1000 results
                print("Using GitHub API method (limited to 1000 proto files)")
                token = os.getenv("GITHUB_TOKEN")
                if token is None:
                    raise ValueError("GITHUB_TOKEN environment variable is not set")
                get_proto_history_parquet(r[0], r[1], token, output_file)
            else:
                # Use local cloning method - no API limits
                if cache_dir:
                    print(f"Using local cloning method with cache directory: {cache_dir}")
                else:
                    print("Using local cloning method (no API limits, requires git)")
                get_proto_history_parquet_local(r[0], r[1], output_file, cache_dir)

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
        df = load_parquet_data(args.parquet_files)

        if args.verbose:
            print("Creating visualizations from proto commit history...")
            print(f"Using data from: {', '.join(args.parquet_files)}")

            # Calculate statistics
            total_files = len(df)
            total_repos = df["repository"].n_unique()
            total_commits = df["commit_count"].sum()
            mean_commits = df["commit_count"].mean()
            min_commits = df["commit_count"].min()
            max_commits = df["commit_count"].max()
            std_commits = df["commit_count"].std()

            print(f"\nCombined Data Summary:")
            print(f"  Total repositories: {total_repos}")
            print(f"  Total proto files: {total_files}")
            print(f"  Total commits: {total_commits}")
            print(f"  Average commits per file: {mean_commits:.2f}")
            print(f"  Min commits per file: {min_commits}")
            print(f"  Max commits per file: {max_commits}")
            print(f"  Standard deviation: {std_commits:.2f}")

            # Show top files by commit count
            top_files = df.sort("commit_count", descending=True).head(5)
            print(f"\nTop files by commit count:")
            for i, row in enumerate(top_files.iter_rows(named=True)):
                print(
                    f"  {i+1}. {row['repository']}:{row['proto_file']}: {row['commit_count']} commits"
                )
            print()

        # Create the requested visualization
        if args.type == "commits":
            if args.verbose:
                print("Creating commit histogram plot...")
            plot_commit_histogram(df, args.output)
        elif args.type == "messages":
            if args.verbose:
                print("Creating message histogram plot...")
            plot_histogram(df, "message_count_total", "Messages", args.output)
        elif args.type == "fields":
            if args.verbose:
                print("Creating files histogram plot...")
            plot_histogram(df, "field_count_total", "Fields", args.output)
        elif args.type == "enums":
            if args.verbose:
                print("Creating enums histogram plot...")
            plot_histogram(df, "enum_count_total", "Enums", args.output)
        elif args.type == "enum_vals":
            if args.verbose:
                print("Creating enum values histogram plot...")
            plot_histogram(df, "enum_count_value", "Enum Values", args.output)
        elif args.type == "services":
            if args.verbose:
                print("Creating services histogram plot...")
            plot_histogram(df, "service_count_total", "Services", args.output)
        elif args.type == "methods":
            if args.verbose:
                print("Creating methods histogram plot...")
            plot_histogram(df, "method_count_total", "Methods", args.output)
        elif args.type == "breakdown":
            if args.verbose:
                print("Creating protobuf type breakdown mosaic plot...")
            plot_proto_type_breakdown(df, args.output)
        elif args.type == "field_types":
            if args.verbose:
                print("Creating field type distribution bar chart...")
            plot_field_type_distribution(df, args.output)

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
    api_file = f"{owner}-{repo}-api.parquet"
    local_file = f"{owner}-{repo}-local.parquet"

    try:
        # Get results from GitHub API
        print("Fetching via GitHub API...")
        get_proto_history_parquet(owner, repo, github_token, api_file)

        # Get results from local cloning
        print("Fetching via local cloning...")
        get_proto_history_parquet_local(owner, repo, local_file)

        # Load both results
        api_df = pl.read_parquet(api_file)
        local_df = pl.read_parquet(local_file)

        # Compare results
        api_files = set(api_df["proto_file"].to_list())
        local_files = set(local_df["proto_file"].to_list())

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
            api_commits = set(api_df.filter(pl.col("proto_file") == file)["commits"][0])
            local_commits = set(
                local_df.filter(pl.col("proto_file") == file)["commits"][0]
            )
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
