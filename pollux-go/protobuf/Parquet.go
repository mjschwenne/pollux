package pollux_proto

import (
	"maps"
	"slices"

	"github.com/parquet-go/parquet-go"
)

// Parquet output exists because the evaluation collects these statistics over
// tens of thousands of files and then loads them into a dataframe. Writing the
// columnar form directly skips the JSON round trip, and lets one invocation
// cover a whole repository instead of one per file.
//
// The column names are the JSON keys: every counter carries a parquet struct
// tag mirroring its json tag, and embedding rather than nesting the counters
// keeps the columns flat.

// StatsRow is one row of the statistics: the file, then its counters.
type StatsRow struct {
	ProtoFile string `parquet:"proto_file"`
	ProtoStats
}

// RecursionRow is one row of the recursion report.
type RecursionRow struct {
	ProtoFile string `parquet:"proto_file"`
	RecursionStats
}

// WriteParquet writes one row per file, sorted by path so that a rerun over the
// same input produces the same file.
func (r StatsResult) WriteParquet(path string) error {
	rows := make([]StatsRow, 0, len(r.Files))
	for _, name := range slices.Sorted(maps.Keys(r.Files)) {
		rows = append(rows, StatsRow{ProtoFile: name, ProtoStats: r.Files[name]})
	}
	return parquet.WriteFile(path, rows)
}

// WriteParquet writes one row per file. The cycles themselves are not in it:
// they are a listing rather than a per-file measurement, and stay in the JSON
// and text renderings.
func (r RecursionReport) WriteParquet(path string) error {
	rows := make([]RecursionRow, 0, len(r.Files))
	for _, name := range slices.Sorted(maps.Keys(r.Files)) {
		rows = append(rows, RecursionRow{ProtoFile: name, RecursionStats: r.Files[name]})
	}
	return parquet.WriteFile(path, rows)
}
