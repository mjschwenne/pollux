import os
import polars as pl

# Handle imports for both script and package usage
try:
    from .eval_fetch import get_proto_history_parquet, get_proto_history_parquet_local
except ImportError:
    from eval_fetch import get_proto_history_parquet, get_proto_history_parquet_local


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


def handle_compare_command(args):
    """
    Main entry point for the compare subcommand.

    Args:
        args: Parsed command-line arguments.
    """
    token = os.getenv("GITHUB_TOKEN")
    if token is None:
        raise ValueError("GITHUB_TOKEN environment variable is not set")

    success = compare_methods(args.owner, args.repo, token)
    if success:
        print("✅ Both methods produced consistent results")
    else:
        print("❌ Methods produced inconsistent results")
