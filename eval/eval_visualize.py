import altair as alt
import polars as pl


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
    """
    Saves an Altair chart to a file or default location.

    Args:
        chart: Altair chart to save.
        output_file: Optional path to save the plot. Format determined by file extension.
    """
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
    Creates a stacked histogram showing the distribution of commits per proto file,
    grouped by usefulness. Useful files are shown at the bottom, with not useful files
    stacked on top in red.

    Args:
        df: Polars DataFrame with commit_count and useful columns.
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """
    # Calculate statistics
    mean_commits = df["commit_count"].mean()
    total_files = len(df)
    total_repos = df["repository"].n_unique()
    useful_count = df.filter(pl.col("useful") == True).shape[0]
    not_useful_count = df.filter(pl.col("useful") == False).shape[0]

    # Add a label column for better display
    df_with_label = df.with_columns(
        pl.when(pl.col("useful"))
        .then(pl.lit("Useful"))
        .otherwise(pl.lit("Not Useful"))
        .alias("usefulness_label")
    )

    # Pre-aggregate data to avoid rendering artifacts
    # Bin the data manually and count by usefulness
    min_val = df["commit_count"].min()
    max_val = df["commit_count"].max()
    bin_width = max(1, (max_val - min_val) / 20)

    aggregated_df = (
        df_with_label.with_columns(
            (
                ((pl.col("commit_count") - min_val) / bin_width).floor().cast(pl.Int64)
            ).alias("bin_index")
        )
        .group_by(["bin_index", "usefulness_label"])
        .agg(pl.len().alias("count"))
        .with_columns(
            ((pl.col("bin_index") * bin_width) + min_val).alias("bin_start"),
            (((pl.col("bin_index") + 1) * bin_width) + min_val).alias("bin_end"),
        )
        .sort(["bin_start", "usefulness_label"])
    )

    # Calculate cumulative positions for stacking
    # Filter out null bin indices to avoid comparison warnings
    aggregated_df = aggregated_df.filter(pl.col("bin_index").is_not_null())
    stacked_df = []
    for bin_idx in aggregated_df["bin_index"].unique().sort():
        bin_data = aggregated_df.filter(pl.col("bin_index") == bin_idx).sort(
            "usefulness_label", descending=True
        )
        cumsum = 0
        for row in bin_data.iter_rows(named=True):
            y_start = cumsum
            y_end = cumsum + row["count"]
            stacked_df.append(
                {
                    "bin_start": row["bin_start"],
                    "bin_end": row["bin_end"],
                    "usefulness_label": row["usefulness_label"],
                    "count": row["count"],
                    "y_start": y_start,
                    "y_end": y_end,
                }
            )
            cumsum = y_end

    aggregated_df = pl.DataFrame(stacked_df)

    # Create stacked bar chart from pre-aggregated data
    histogram = (
        alt.Chart(aggregated_df)
        .mark_rect()
        .encode(
            alt.X(
                "bin_start:Q",
                title="Number of Commits per Proto File",
                axis=alt.Axis(tickMinStep=1, format=".0f"),
                scale=alt.Scale(domain=[min_val, max_val]),
            ),
            alt.X2("bin_end:Q"),
            alt.Y(
                "y_start:Q", title="Number of Proto Files", axis=alt.Axis(grid=False)
            ),
            alt.Y2("y_end:Q"),
            alt.Color(
                "usefulness_label:N",
                title="File Type",
                scale=alt.Scale(
                    domain=["Useful", "Not Useful"], range=["steelblue", "red"]
                ),
                sort=["Useful", "Not Useful"],
            ),
            order=alt.Order("usefulness_label:N", sort="descending"),
            tooltip=[
                alt.Tooltip("usefulness_label:N", title="Type"),
                alt.Tooltip("count:Q", title="Count"),
                alt.Tooltip("bin_start:Q", title="Commits (bin start)"),
            ],
        )
        .properties(
            width=600,
            height=400,
            title=[
                f"Distribution of Commits per Proto File",
                f"{total_files} files from {total_repos} repositories (Mean: {mean_commits:.2f})",
                f"Useful: {useful_count}, Not Useful: {not_useful_count}",
            ],
        )
    )

    # Create vertical line for mean
    mean_df = pl.DataFrame({"mean": [mean_commits], "legend": ["Mean"]})
    mean_line = (
        alt.Chart(mean_df)
        .mark_rule(color="orange", strokeWidth=2, strokeDash=[5, 5])
        .encode(
            x=alt.X("mean:Q", axis=alt.Axis(tickMinStep=1)),
            color=alt.Color(
                "legend:N",
                scale=alt.Scale(range=["orange"]),
                legend=alt.Legend(title="Statistics"),
            ),
        )
    )

    # Combine histogram and mean line with independent color scales
    chart = (histogram + mean_line).resolve_scale(color="independent")

    # Save or display
    save_plot(chart, output_file)

    return chart


def plot_histogram(
    df: pl.DataFrame, attr: str, attr_name: str, output_file: str | None = None
) -> alt.Chart | alt.LayerChart:
    """
    Creates a stacked histogram showing the distribution the given dataframe attribute,
    grouped by usefulness. Useful files are shown at the bottom, with not useful files
    stacked on top in red.

    Args:
        df: Loaded data frame
        attr: The column name in df to plot
        attr_name: Human-readable name for the attribute
        output_file: Optional path to save the plot. Format determined by file extension (.png, .html, etc.)

    Returns:
        Altair Chart or LayerChart object
    """

    if attr not in df.columns:
        raise ValueError(
            f"'{attr}' columns not found in data. Exclude the --api flag when fetching to get full stats."
        )

    mean = df[attr].mean()
    useful_count = df.filter(pl.col("useful") == True).shape[0]
    not_useful_count = df.filter(pl.col("useful") == False).shape[0]

    # Add a label column for better display
    df_with_label = df.with_columns(
        pl.when(pl.col("useful"))
        .then(pl.lit("Useful"))
        .otherwise(pl.lit("Not Useful"))
        .alias("usefulness_label")
    )

    # Pre-aggregate data to avoid rendering artifacts
    # Bin the data manually and count by usefulness
    min_val = df[attr].min()
    max_val = df[attr].max()
    attr_range = max_val - min_val
    bin_width = max(1, attr_range / 20) if attr_range > 0 else 1

    aggregated_df = (
        df_with_label.with_columns(
            (((pl.col(attr) - min_val) / bin_width).floor().cast(pl.Int64)).alias(
                "bin_index"
            )
        )
        .group_by(["bin_index", "usefulness_label"])
        .agg(pl.len().alias("count"))
        .with_columns(
            ((pl.col("bin_index") * bin_width) + min_val).alias("bin_start"),
            (((pl.col("bin_index") + 1) * bin_width) + min_val).alias("bin_end"),
        )
        .sort(["bin_start", "usefulness_label"])
    )

    # Calculate cumulative positions for stacking
    # Filter out null bin indices to avoid comparison warnings
    aggregated_df = aggregated_df.filter(pl.col("bin_index").is_not_null())
    stacked_df = []
    for bin_idx in aggregated_df["bin_index"].unique().sort():
        bin_data = aggregated_df.filter(pl.col("bin_index") == bin_idx).sort(
            "usefulness_label", descending=True
        )
        cumsum = 0
        for row in bin_data.iter_rows(named=True):
            y_start = cumsum
            y_end = cumsum + row["count"]
            stacked_df.append(
                {
                    "bin_start": row["bin_start"],
                    "bin_end": row["bin_end"],
                    "usefulness_label": row["usefulness_label"],
                    "count": row["count"],
                    "y_start": y_start,
                    "y_end": y_end,
                }
            )
            cumsum = y_end

    aggregated_df = pl.DataFrame(stacked_df)

    histogram = (
        alt.Chart(aggregated_df)
        .mark_rect()
        .encode(
            alt.X(
                "bin_start:Q",
                title=f"Number of {attr_name} per Proto File",
                axis=alt.Axis(tickMinStep=1, format=".0f"),
                scale=alt.Scale(domain=[min_val, max_val]),
            ),
            alt.X2("bin_end:Q"),
            alt.Y(
                "y_start:Q", title="Number of Proto Files", axis=alt.Axis(grid=False)
            ),
            alt.Y2("y_end:Q"),
            alt.Color(
                "usefulness_label:N",
                title="File Type",
                scale=alt.Scale(
                    domain=["Useful", "Not Useful"], range=["steelblue", "red"]
                ),
                sort=["Useful", "Not Useful"],
            ),
            order=alt.Order("usefulness_label:N", sort="descending"),
            tooltip=[
                alt.Tooltip("usefulness_label:N", title="Type"),
                alt.Tooltip("count:Q", title="Count"),
                alt.Tooltip("bin_start:Q", title=f"{attr_name} (bin start)"),
            ],
        )
        .properties(
            width=600,
            height=400,
            title=[
                f"Distribution of {attr_name} per Proto File",
                f"{len(df)} files from {df['repository'].n_unique()} repositories (Mean: {mean:.2f})",
                f"Useful: {useful_count}, Not Useful: {not_useful_count}",
            ],
        )
    )

    mean_df = pl.DataFrame({"mean": [mean], "legend": ["Mean"]})
    mean_line = (
        alt.Chart(mean_df)
        .mark_rule(color="orange", strokeWidth=2, strokeDash=[5, 5])
        .encode(
            x=alt.X("mean:Q", axis=alt.Axis(tickMinStep=1)),
            color=alt.Color(
                "legend:N",
                scale=alt.Scale(range=["orange"]),
                legend=alt.Legend(title="Statistics"),
            ),
        )
    )

    # Combine histogram and mean line with independent color scales
    chart = (histogram + mean_line).resolve_scale(color="independent")

    # Save or display
    save_plot(chart, output_file)

    return chart


def plot_proto_type_breakdown(
    df: pl.DataFrame, output_file: str | None = None
) -> alt.LayerChart:
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
                "Protobuf Top LeBreakdown by Repository",
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


def handle_visualize_command(args):
    """
    Main entry point for the visualize subcommand.

    Args:
        args: Parsed command-line arguments.
    """
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
