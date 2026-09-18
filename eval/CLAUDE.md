# CLAUDE.md: Evaluation Pipeline

`eval/` mines real-world `.proto` corpora (and Go JSON struct tags) for the statistics the report cites and the design leans on. Examples are the recursion tables in `sec:proto-desc` (`tab:recur-summary`, `tab:recur-repos`), which decided when Lean needs a symbol-table descriptor, and the data-source tables in the evaluation section (`tbl:proto-sources`, `tbl:json-sources`). `README.org` is the full manual; read it before running anything.

## The Report Boundary

The report's numbers are **hard-coded in the `.tex`**, not generated from here. If a change in `eval/` (or in the `pollux` binary it calls) moves a number, a table, or a figure the report cites, don't touch the report. Write a note in `notes/` naming the table or figure `\label`, the old and new values, and the cause. The author updates the report.

## Running It

```bash
nix develop .#eval      # Python 3.14 (polars, altair, vl-convert, requests, rich), pyright, nushell + polars plugin, gh, jq
python eval.py fetch --repo <owner> <repo> --output data-proto
python eval.py visualize data-proto/*.parquet --type recursion --output recursion.png
python eval.py compare <owner> <repo>
```

- `fetch` shells out to `pollux proto stats` via `which pollux`. The `pollux` on `PATH` decides which Parquet columns exist, and a dev shell pins it at entry. After rebuilding `pollux-go`, leave and re-enter the shell, then check with `pollux proto stats --help | grep parquet`.
- **Ask before `fetch --all`.** It clones every repository in `PROTO_REPOS`, googleapis included, and takes a long time and a lot of network. It also moves the dataset to whatever the repositories hold today, which changes the report's numbers. Single-repo fetches are fine.
- `--error-log` appends and never truncates. Delete the log first if the point is to count current failures.
- Combining Parquet files keeps only their shared columns. A "Missing required columns" error means some file predates a counter; refetch that file.
- `--api` needs `GITHUB_TOKEN` (exported by the root dev shell) and collects no statistics, so only the `commits` plot works on API data.

## Layout

| Path                                              | Role                                                                       |
|---------------------------------------------------|----------------------------------------------------------------------------|
| `eval.py`                                         | CLI entry: `fetch`, `visualize`, `compare` subcommands                     |
| `eval_fetch.py`                                   | cloning, import-path inference, `pollux proto stats` calls, JSON-tag search |
| `eval_visualize.py`                               | Altair plots (`--type commits\|messages\|fields\|…\|recursion`)             |
| `eval_compare.py`                                 | local-clone vs. GitHub API cross-check                                     |
| `eval_utils.py`                                   | `PROTO_REPOS`, `JSON_REPOS`, `locate_pollux`, paginated GitHub queries     |
| `pollux.nu`                                       | Nushell helpers for ad-hoc Parquet queries (`pollux-nu load-data`, `json top-n`, …) |
| `data-proto/`, `data-go-json/`, `data-go-json-api/` | tracked Parquet datasets, one file per repository                        |
| `*.png`, `*-summary.txt`, `*-stats.txt`           | tracked outputs from earlier runs                                          |

The dataset is tracked in git, so a refetch shows up as a diff. Don't commit a regenerated dataset unless the author asked for the refresh.

`pyright` is the type checker in the dev shell. The code uses type hints, so keep them.
