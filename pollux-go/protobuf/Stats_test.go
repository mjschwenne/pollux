package pollux_proto

import (
	"encoding/json"
	"maps"
	"slices"
	"testing"
)

// Maps compile to a repeated field of a synthetic entry message. The entry
// carries a map_entry option, so it can be counted exactly rather than guessed
// at from the name -- which matters, because a hand written message is allowed
// to be named FooEntry too.
func TestMapCounts(t *testing.T) {
	t.Chdir("../testdata/proto")

	var stats map[string]ProtoStats
	if err := json.Unmarshal(ComputeStats([]string{"maps.proto"}), &stats); err != nil {
		t.Fatalf("decoding the statistics: %v", err)
	}
	got := stats["maps.proto"]

	tests := []struct {
		key  string
		got  uint64
		want uint64
	}{
		// Inventory, Item, Inventory.TagEntry, and the two synthetic
		// entries for the two maps.
		{key: "message_count_total", got: got.MsgC, want: 5},
		// Only the two synthetic ones: TagEntry is a real message.
		{key: "message_count_map_entry", got: got.M_MapEntryC, want: 2},
		{key: "field_count_map", got: got.F_MapC, want: 2},
		// The three fields of Inventory, one of Item, and the key and
		// value of each of the three Entry messages.
		{key: "field_count_total", got: got.FieldC, want: 10},
		// Both maps plus tags. A map field is repeated, and is still
		// counted as such.
		{key: "field_count_repeated", got: got.F_RepC, want: 3},
	}
	for _, tt := range tests {
		if tt.got != tt.want {
			t.Errorf("%s: got %d, want %d", tt.key, tt.got, tt.want)
		}
	}

	// The point of the counter: recovering the number of messages actually
	// written down in the file.
	if declared := got.MsgC - got.M_MapEntryC; declared != 3 {
		t.Errorf("declared messages: got %d, want 3", declared)
	}
}

func TestMapCountsNoMaps(t *testing.T) {
	t.Chdir("../testdata/proto/recursion")

	var stats map[string]ProtoStats
	if err := json.Unmarshal(ComputeStats([]string{"imports.proto"}), &stats); err != nil {
		t.Fatalf("decoding the statistics: %v", err)
	}
	if got := stats["imports.proto"]; got.M_MapEntryC != 0 || got.F_MapC != 0 {
		t.Errorf("got %d map entries and %d map fields, want none",
			got.M_MapEntryC, got.F_MapC)
	}
}

// The statistics are keyed by the paths given, not by the names the compiler
// knows the files under, so that the caller passing paths from `find` together
// with an import path can join the answer against its own list.
func TestStatsKeyedByGivenPath(t *testing.T) {
	const path = "../testdata/proto/recursion/imports.proto"
	result := AnalyzeStats([]string{path}, []string{"../testdata/proto/recursion"})

	if len(result.Errors) != 0 {
		t.Fatalf("got errors %v, want none", result.Errors)
	}
	got, ok := result.Files[path]
	if !ok {
		t.Fatalf("got rows for %v, want one named %s", slices.Sorted(maps.Keys(result.Files)), path)
	}
	// The import path did its job: without it the file does not compile,
	// and with it Config reaches the cycle among the well-known Struct,
	// Value and ListValue.
	if got.M_ContainsRecC != 1 {
		t.Errorf("got %+v, want one message containing recursion", got)
	}
}
