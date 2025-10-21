"""
Evaluation utilities for the Pollux project.

This package contains tools for fetching, analyzing, and visualizing
protobuf repository data from GitHub.
"""

from .eval_utils import PROTO_REPOS, locate_pollux, paginated_github_query
from .eval_fetch import (
    search_popular_go_repositories,
    get_json_usage_parquet,
    get_proto_history_parquet,
    get_proto_history_parquet_local,
    handle_fetch_command,
)
from .eval_visualize import (
    load_parquet_data,
    save_plot,
    plot_commit_histogram,
    plot_histogram,
    plot_proto_type_breakdown,
    plot_field_type_distribution,
    handle_visualize_command,
)
from .eval_compare import (
    compare_methods,
    handle_compare_command,
)

__all__ = [
    # Utils
    "PROTO_REPOS",
    "locate_pollux",
    "paginated_github_query",
    # Fetch
    "search_popular_go_repositories",
    "get_json_usage_parquet",
    "get_proto_history_parquet",
    "get_proto_history_parquet_local",
    "handle_fetch_command",
    # Visualize
    "load_parquet_data",
    "save_plot",
    "plot_commit_histogram",
    "plot_histogram",
    "plot_proto_type_breakdown",
    "plot_field_type_distribution",
    "handle_visualize_command",
    # Compare
    "compare_methods",
    "handle_compare_command",
]
