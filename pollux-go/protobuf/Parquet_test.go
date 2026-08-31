package pollux_proto

import (
	"path/filepath"
	"testing"

	"github.com/parquet-go/parquet-go"
)

// The parquet form has to carry the same column names as the JSON form, since
// the evaluation loads either one into the same dataframe.
func TestWriteStatsParquet(t *testing.T) {
	t.Chdir("../testdata/proto")
	out := filepath.Join(t.TempDir(), "stats.parquet")

	result := AnalyzeStats([]string{"maps.proto"}, nil)
	if err := result.WriteParquet(out); err != nil {
		t.Fatalf("writing %s: %v", out, err)
	}

	rows, err := parquet.ReadFile[StatsRow](out)
	if err != nil {
		t.Fatalf("reading %s: %v", out, err)
	}
	if len(rows) != 1 {
		t.Fatalf("got %d rows, want 1", len(rows))
	}
	if rows[0].ProtoFile != "maps.proto" {
		t.Errorf("proto_file: got %q, want maps.proto", rows[0].ProtoFile)
	}
	if rows[0].MsgC != 5 || rows[0].M_MapEntryC != 2 {
		t.Errorf("got %d messages and %d map entries, want 5 and 2",
			rows[0].MsgC, rows[0].M_MapEntryC)
	}

	// The counters embedded from RecursionStats have to land as flat
	// columns rather than a nested group.
	schema := parquet.SchemaOf(StatsRow{})
	for _, name := range []string{"proto_file", "message_count_total", "message_count_map_entry", "message_count_recursive"} {
		if _, ok := schema.Lookup(name); !ok {
			t.Errorf("no column named %s", name)
		}
	}
}

func TestWriteRecursionParquet(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")
	out := filepath.Join(t.TempDir(), "recursion.parquet")

	report := AnalyzeRecursion([]string{"recursion.proto"}, nil)
	if err := report.WriteParquet(out); err != nil {
		t.Fatalf("writing %s: %v", out, err)
	}

	rows, err := parquet.ReadFile[RecursionRow](out)
	if err != nil {
		t.Fatalf("reading %s: %v", out, err)
	}
	if len(rows) != 1 {
		t.Fatalf("got %d rows, want 1", len(rows))
	}
	if rows[0].M_RecursiveC != 10 || rows[0].M_ContainsRecC != 12 {
		t.Errorf("got %d recursive and %d containing recursion, want 10 and 12",
			rows[0].M_RecursiveC, rows[0].M_ContainsRecC)
	}
}
