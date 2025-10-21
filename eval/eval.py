import argparse
import sys
import os

# Add parent directory to path to allow imports when run as script
if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from eval_fetch import handle_fetch_command
    from eval_visualize import handle_visualize_command
    from eval_compare import handle_compare_command
else:
    from .eval_fetch import handle_fetch_command
    from .eval_visualize import handle_visualize_command
    from .eval_compare import handle_compare_command


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
    fetch_parser = subparsers.add_parser(
        "fetch", help="Fetch commit history from GitHub"
    )
    ty = fetch_parser.add_mutually_exclusive_group(required=True)
    ty.add_argument(
        "--all", "-a", action="store_true", help="Fetch data from all repositories"
    )
    ty.add_argument("--repo", "-r", nargs=2, help="Fetch data from a specific repository")
    ty.add_argument(
        "--search-go-repos",
        action="store_true",
        help="Search for popular Go repositories"
    )
    fetch_parser.add_argument(
        "--api",
        action="store_true",
        help="Perform a limited analysis using the GitHub REST API. Doesn't download anything, but does require GITHUB_TOKEN env var to be set.",
    )
    fetch_parser.add_argument(
        "--cache",
        type=str,
        help="Cache directory path. Repos will be cached as <owner>-<repo>. If not provided, uses temporary directory.",
    )
    fetch_parser.add_argument(
        "--output",
        help="Path to output the Parquet file in. Each repo will be output as <owner>-<repo>.parquet",
    )
    fetch_parser.add_argument(
        "--error-log",
        type=str,
        help="Path to log errors to disk. Errors will be appended to this file with repository context.",
    )
    fetch_parser.add_argument("--json-usage",
        action="store_true",
        help="Analyze if the repo is using JSON tags")

    # Subparser for comparing methods
    compare_parser = subparsers.add_parser(
        "compare", help="Compare GitHub API and local cloning methods"
    )
    compare_parser.add_argument("owner", help="GitHub repository owner/username")
    compare_parser.add_argument("repo", help="GitHub repository name")

    # Subparser for visualization
    viz_parser = subparsers.add_parser(
        "visualize", help="Create visualizations from Parquet data"
    )
    viz_parser.add_argument(
        "parquet_files",
        nargs="+",
        help="Path(s) to Parquet file(s) created by fetch command",
    )
    viz_parser.add_argument(
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
    viz_parser.add_argument(
        "--output",
        help="Output file path for saving the plot (format determined by file extension: .png, .html, etc.)",
    )
    viz_parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed statistics about the data",
    )

    args = parser.parse_args()

    if args.command == "fetch":
        handle_fetch_command(args)
    elif args.command == "compare":
        handle_compare_command(args)
    elif args.command == "visualize":
        handle_visualize_command(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
