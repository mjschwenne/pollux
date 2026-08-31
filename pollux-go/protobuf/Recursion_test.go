package pollux_proto

import (
	"encoding/json"
	"maps"
	"slices"
	"strings"
	"testing"
)

func TestRecursionReport(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")
	report := AnalyzeRecursion([]string{"recursion.proto"}, nil)

	want := RecursionStats{
		M_RecursiveC:   10,
		M_SelfRecC:     3,
		M_MutualRecC:   7,
		M_ContainsRecC: 12,
		RecGroupC:      6,
		RecGroupMaxC:   3,
	}
	if got := report.Files["recursion.proto"]; got != want {
		t.Errorf("per-file counters: got %+v, want %+v", got, want)
	}
	if report.Totals.RecursionStats != want {
		t.Errorf("totals: got %+v, want %+v", report.Totals.RecursionStats, want)
	}
	// Map entries are not messages here, unlike in the stats command.
	if report.Totals.MsgC != 15 {
		t.Errorf("message count: got %d, want 15", report.Totals.MsgC)
	}

	if len(report.Groups) != 6 {
		t.Fatalf("got %d cycles, want 6", len(report.Groups))
	}
	self := report.Groups[slices.IndexFunc(report.Groups, func(g RecursionGroupReport) bool {
		return slices.Contains(g.Messages, "rec.MapNode")
	})]
	if self.Size != 1 || !self.Self || self.Mutual {
		t.Errorf("rec.MapNode cycle: got %+v, want a self recursive cycle of one", self)
	}
	if len(self.Edges) != 1 || !self.Edges[0].Map || self.Edges[0].Label != "map" {
		t.Errorf("rec.MapNode cycle edges: got %+v, want one map edge", self.Edges)
	}
}

// A file with no recursion still gets a row, so that a caller can tell "found
// none" from "not analyzed".
func TestRecursionReportEmptyFile(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")
	report := AnalyzeRecursion([]string{"imports.proto"}, nil)

	got, ok := report.Files["imports.proto"]
	if !ok {
		t.Fatal("no row for imports.proto")
	}
	if got.M_RecursiveC != 0 || got.RecGroupC != 0 {
		t.Errorf("got %+v, want no recursion", got)
	}
	// The cycle among Struct, Value and ListValue belongs to the imported
	// file, so it is not reported, but Config can still reach it.
	if len(report.Groups) != 0 {
		t.Errorf("got %d cycles from an imported file, want none", len(report.Groups))
	}
	if got.M_ContainsRecC != 1 {
		t.Errorf("got %d messages containing recursion, want 1", got.M_ContainsRecC)
	}
}

func TestRecursionReportJSON(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")

	var decoded struct {
		Totals map[string]any            `json:"totals"`
		Files  map[string]map[string]any `json:"files"`
	}
	if err := json.Unmarshal(AnalyzeRecursion([]string{"recursion.proto"}, nil).JSON(), &decoded); err != nil {
		t.Fatalf("decoding the report: %v", err)
	}
	if got := decoded.Files["recursion.proto"]["message_count_recursive"]; got != float64(10) {
		t.Errorf("message_count_recursive: got %v, want 10", got)
	}
	if got := decoded.Totals["message_count_total"]; got != float64(15) {
		t.Errorf("message_count_total: got %v, want 15", got)
	}
}

// The recursion counters ride along with the rest of the per-file statistics,
// which is how the dataset survey picks them up.
func TestStatsCarryRecursion(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")

	var stats map[string]ProtoStats
	if err := json.Unmarshal(ComputeStats([]string{"recursion.proto"}), &stats); err != nil {
		t.Fatalf("decoding the statistics: %v", err)
	}

	got := stats["recursion.proto"].RecursionStats
	want := RecursionStats{
		M_RecursiveC:   10,
		M_SelfRecC:     3,
		M_MutualRecC:   7,
		M_ContainsRecC: 12,
		RecGroupC:      6,
		RecGroupMaxC:   3,
	}
	if got != want {
		t.Errorf("got %+v, want %+v", got, want)
	}
	// The message count keeps counting the two synthetic map entries that
	// the recursion counters leave out.
	if c := stats["recursion.proto"].MsgC; c != 17 {
		t.Errorf("message_count_total: got %d, want 17", c)
	}
}

// Two copies of a schema at different paths define the same symbols, so they
// cannot share a compilation. The report falls back to compiling each on its
// own rather than giving up.
func TestDuplicateSymbolsAcrossFiles(t *testing.T) {
	t.Chdir("../testdata/proto/collide")
	report := AnalyzeRecursion([]string{"a/dup.proto", "b/dup.proto"}, nil)

	if len(report.Errors) != 0 {
		t.Fatalf("got errors %v, want none", report.Errors)
	}
	for _, path := range []string{"a/dup.proto", "b/dup.proto"} {
		got, ok := report.Files[path]
		if !ok {
			t.Errorf("no row for %s", path)
			continue
		}
		if got.M_SelfRecC != 1 || got.RecGroupC != 1 {
			t.Errorf("%s: got %+v, want one self recursive message", path, got)
		}
	}
	if report.Totals.FileC != 2 || report.Totals.MsgC != 2 {
		t.Errorf("totals: got %d files and %d messages, want 2 and 2",
			report.Totals.FileC, report.Totals.MsgC)
	}
}

// One file that does not compile should cost only that file.
func TestFileThatDoesNotCompile(t *testing.T) {
	t.Chdir("../testdata/proto/collide")
	report := AnalyzeRecursion([]string{"a/dup.proto", "does_not_compile.proto"}, nil)

	if _, ok := report.Errors["does_not_compile.proto"]; !ok {
		t.Errorf("got errors %v, want does_not_compile.proto among them", report.Errors)
	}
	if _, ok := report.Files["a/dup.proto"]; !ok {
		t.Error("a/dup.proto was not analyzed")
	}
	if report.Totals.FileC != 1 {
		t.Errorf("file count: got %d, want 1", report.Totals.FileC)
	}
}

// A file given twice is one file, not two.
func TestDuplicateArguments(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")
	report := AnalyzeRecursion([]string{"recursion.proto", "recursion.proto"}, nil)

	if report.Totals.FileC != 1 || report.Totals.MsgC != 15 {
		t.Errorf("totals: got %d files and %d messages, want 1 and 15",
			report.Totals.FileC, report.Totals.MsgC)
	}
	if len(report.Groups) != 6 {
		t.Errorf("got %d cycles, want 6", len(report.Groups))
	}
}

// The compiler knows a file by its name relative to the import path it sits
// under, but the report is keyed by the path the caller gave, so that passing
// paths from `find` together with an import path still yields rows the caller
// can find its own files in.
func TestImportPathNaming(t *testing.T) {
	const path = "../testdata/proto/recursion/imports.proto"
	report := AnalyzeRecursion([]string{path}, []string{"../testdata/proto/recursion"})

	got, ok := report.Files[path]
	if !ok {
		t.Fatalf("got rows for %v, want one named %s", slices.Sorted(maps.Keys(report.Files)), path)
	}
	// The import path did its job: Config reaches the cycle among the
	// well-known Struct, Value and ListValue.
	if got.M_ContainsRecC != 1 {
		t.Errorf("got %+v, want one message containing recursion", got)
	}
}

// Two copies of one schema, each under an import path of its own, want the same
// name. The compiler answers a name with exactly one file, so the copy it would
// not answer with is left out and said so, rather than being reported with the
// other copy's numbers.
func TestShadowedCopyIsReported(t *testing.T) {
	t.Chdir("../testdata/proto/collide")
	report := AnalyzeRecursion([]string{"a/dup.proto", "b/dup.proto"}, []string{"a", "b"})

	if _, ok := report.Files["a/dup.proto"]; !ok {
		t.Errorf("got rows for %v, want one for a/dup.proto",
			slices.Sorted(maps.Keys(report.Files)))
	}
	why, ok := report.Errors["b/dup.proto"]
	if !ok {
		t.Fatalf("got errors %v, want b/dup.proto among them", report.Errors)
	}
	if !strings.Contains(why, "dup.proto") {
		t.Errorf("reason %q does not name the file that claims the name", why)
	}
}
