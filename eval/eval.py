import requests
import json
import time
import argparse
from typing import Dict, List, Optional, Union
from rich.progress import Progress, TaskID
import altair as alt
import pandas as pd
import numpy as np

import os

def get_proto_history_json(owner: str, repo: str, github_token: str) -> None:
    """
    Fetches the commit history for all .proto files in a GitHub repository
    and saves the result as a JSON file.

    Args:
        owner: GitHub repository owner.
        repo: GitHub repository name.
        github_token: GitHub personal access token for authentication.
    """
    # Step 1: Search for .proto files
    search_url = f"https://api.github.com/search/code?q=extension:proto+repo:{owner}/{repo}"
    headers = {"Authorization": f"token {github_token}", "Accept": "application/vnd.github.v3+json"}
    response = requests.get(search_url, headers=headers)
    response.raise_for_status()
    proto_files = [item["path"] for item in response.json()["items"]]
    nproto = len(proto_files)
    print(f"Found {nproto} proto files in {owner}/{repo}")

    # Initialize JSON output
    json_output: Dict[str, List[str]] = {}

    # Step 2: Fetch commit history for each .proto file
    with Progress() as progress:
        task = progress.add_task("[green]Processing proto files...", total=nproto)

        for file in proto_files:
            commits_url = f"https://api.github.com/repos/{owner}/{repo}/commits?path={file}"
            response = requests.get(commits_url, headers=headers)
            response.raise_for_status()
            commits = response.json()
            commit_hashes = [commit["sha"] for commit in commits]
            json_output[file] = commit_hashes

            progress.update(task, advance=1)
            time.sleep(1)  # Avoid rate limiting

    # Step 3: Save JSON output
    output_filename = f"{owner}-{repo}.json"
    with open(output_filename, "w") as f:
        json.dump(json_output, f, indent=2)
        f.write("\n")
    print(f"\n\nSaved commit history to {output_filename}")

def plot_commit_histogram(json_file: str, output_file: Optional[str] = None) -> Union[alt.Chart, alt.LayerChart]:
    """
    Creates a histogram showing the distribution of commits per proto file.

    Args:
        json_file: Path to the JSON file output by get_proto_history_json
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """
    # Load the JSON data
    with open(json_file, 'r') as f:
        data = json.load(f)

    # Count commits per file
    commit_counts = [len(commits) for commits in data.values()]

    # Calculate statistics
    mean_commits = np.mean(commit_counts)

    # Create DataFrame for Altair
    df = pd.DataFrame({
        'proto_file': list(data.keys()),
        'commit_count': commit_counts
    })

    # Create base chart
    base = alt.Chart(df)

    # Create histogram with explicit integer bins
    min_commits = min(commit_counts)
    max_commits = max(commit_counts)

    histogram = base.mark_bar(
        opacity=0.7,
        color='steelblue'
    ).encode(
        alt.X('commit_count:Q',
              bin=alt.Bin(extent=[min_commits - 0.5, max_commits + 0.5], step=1),
              title='Number of Commits per Proto File',
              axis=alt.Axis(tickMinStep=1)),
        alt.Y('count()', title='Number of Proto Files'),
        tooltip=['count()', 'commit_count:Q']
    ).properties(
        width=600,
        height=400,
        title=f'Distribution of Commits per Proto File (Mean: {mean_commits:.2f})'
    )

    # Create vertical line for mean with legend
    mean_line = alt.Chart(pd.DataFrame({'mean': [mean_commits], 'legend': ['Mean']})).mark_rule(
        color='red',
        strokeWidth=2,
        strokeDash=[5, 5]
    ).encode(
        x=alt.X('mean:Q', axis=alt.Axis(tickMinStep=1)),
        color=alt.Color('legend:N', scale=alt.Scale(range=['red']), legend=alt.Legend(title="Statistics"))
    )

    # Combine histogram and mean line
    chart = histogram + mean_line

    # Save or display
    if output_file:
        # Determine format from file extension
        if output_file.endswith('.png'):
            chart.save(output_file, scale_factor=2.0)
            print(f"Plot saved to {output_file}")
        elif output_file.endswith('.html') or '.' not in output_file:
            # Default to HTML if no extension or explicit .html
            if '.' not in output_file:
                output_file += '.html'
            chart.save(output_file)
            print(f"Plot saved to {output_file}")
        else:
            # Try to save with whatever extension was provided
            chart.save(output_file)
            print(f"Plot saved to {output_file}")
    else:
        chart.show()

    return chart

def plot_commit_kde(json_file: str, output_file: Optional[str] = None) -> Union[alt.Chart, alt.LayerChart]:
    """
    Creates a kernel density estimation plot showing the distribution of commits per proto file.

    Args:
        json_file: Path to the JSON file output by get_proto_history_json
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """
    # Load the JSON data
    with open(json_file, 'r') as f:
        data = json.load(f)

    # Count commits per file
    commit_counts = [len(commits) for commits in data.values()]

    # Calculate statistics
    mean_commits = np.mean(commit_counts)

    # Create DataFrame for Altair
    df = pd.DataFrame({
        'proto_file': list(data.keys()),
        'commit_count': commit_counts
    })

    # Create KDE plot using density transform
    kde_plot = alt.Chart(df).transform_density(
        'commit_count',
        as_=['commit_count', 'density'],
        extent=[min(commit_counts), max(commit_counts)]
    ).mark_area(
        opacity=0.7,
        color='lightblue',
        stroke='steelblue',
        strokeWidth=2
    ).encode(
        alt.X('commit_count:Q',
              title='Number of Commits',
              axis=alt.Axis(tickMinStep=1, format='.0f')),
        alt.Y('density:Q', title='Density')
    ).properties(
        width=600,
        height=400,
        title=f'Kernel Density Estimate of Commits per Proto File (Mean: {mean_commits:.2f})'
    )

    # Create vertical line for mean with legend
    mean_line = alt.Chart(pd.DataFrame({'mean': [mean_commits], 'legend': ['Mean']})).mark_rule(
        color='red',
        strokeWidth=2,
        strokeDash=[5, 5]
    ).encode(
        x=alt.X('mean:Q', axis=alt.Axis(tickMinStep=1)),
        color=alt.Color('legend:N', scale=alt.Scale(range=['red']), legend=alt.Legend(title="Statistics"))
    )

    # Combine KDE and mean line
    chart = kde_plot + mean_line

    # Save or display
    if output_file:
        # Determine format from file extension
        if output_file.endswith('.png'):
            chart.save(output_file, scale_factor=2.0)
            print(f"KDE plot saved to {output_file}")
        elif output_file.endswith('.html') or '.' not in output_file:
            # Default to HTML if no extension or explicit .html
            if '.' not in output_file:
                output_file += '.html'
            chart.save(output_file)
            print(f"KDE plot saved to {output_file}")
        else:
            # Try to save with whatever extension was provided
            chart.save(output_file)
            print(f"KDE plot saved to {output_file}")
    else:
        chart.show()

    return chart

def main():
    parser = argparse.ArgumentParser(description="Fetch commit history for .proto files in a GitHub repository or visualize existing data")

    # Create subparsers for different commands
    subparsers = parser.add_subparsers(dest='command', help='Available commands')

    # Subparser for fetching data
    fetch_parser = subparsers.add_parser('fetch', help='Fetch commit history from GitHub')
    fetch_parser.add_argument("owner", help="GitHub repository owner/username")
    fetch_parser.add_argument("repo", help="GitHub repository name")

    # Subparser for visualization
    viz_parser = subparsers.add_parser('visualize', help='Create visualizations from JSON data')
    viz_parser.add_argument("json_file", help="Path to JSON file created by get_proto_history_json")
    viz_parser.add_argument("--type", choices=['histogram', 'kde'], default='histogram',
                           help="Type of plot to create (default: histogram)")
    viz_parser.add_argument("--output", help="Output file path for saving the plot (format determined by file extension: .png, .html, etc.)")
    viz_parser.add_argument("--verbose", "-v", action="store_true", help="Show detailed statistics about the data")

    args = parser.parse_args()

    if args.command == 'fetch':
        token = os.getenv("GITHUB_TOKEN")
        if token is None:
            raise ValueError("GITHUB_TOKEN environment variable is not set")
        get_proto_history_json(args.owner, args.repo, token)

    elif args.command == 'visualize':
        # Load and analyze data if verbose mode is requested
        if args.verbose:
            print("Creating visualizations from proto commit history...")
            print(f"Using data from: {args.json_file}")

            # Load and examine the data
            with open(args.json_file, 'r') as f:
                data = json.load(f)

            # Print some basic statistics
            commit_counts = [len(commits) for commits in data.values()]
            print(f"\nData Summary:")
            print(f"  Total proto files: {len(data)}")
            print(f"  Total commits: {sum(commit_counts)}")
            print(f"  Average commits per file: {np.mean(commit_counts):.2f}")
            print(f"  Min commits per file: {min(commit_counts)}")
            print(f"  Max commits per file: {max(commit_counts)}")
            print(f"  Standard deviation: {np.std(commit_counts):.2f}")

            # Show files with most commits
            file_commit_pairs = [(file, len(commits)) for file, commits in data.items()]
            file_commit_pairs.sort(key=lambda x: x[1], reverse=True)

            print(f"\nTop files by commit count:")
            for i, (file, count) in enumerate(file_commit_pairs[:5]):
                print(f"  {i+1}. {file}: {count} commits")
            print()

        # Create the requested visualization
        if args.type == 'histogram':
            if args.verbose:
                print("Creating histogram plot...")
            plot_commit_histogram(args.json_file, args.output)
        elif args.type == 'kde':
            if args.verbose:
                print("Creating KDE plot...")
            plot_commit_kde(args.json_file, args.output)

        if args.verbose:
            print("\nVisualization complete!")

    else:
        parser.print_help()

if __name__ == "__main__":
    main()
