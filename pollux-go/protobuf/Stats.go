package pollux_proto

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"slices"
	"strings"

	"github.com/bufbuild/protocompile/walk"
	"google.golang.org/protobuf/reflect/protoreflect"

	"github.com/mjschwenne/pollux/internal/desclib"
)

// RecursionStats counts how the messages of one file sit in the message
// reference graph. The graph spans every file imported by the one being
// summarized -- which is what makes message_count_contains_recursive right for
// a message whose only recursion comes from an imported type -- but only
// messages declared in this file contribute to these counts.
//
// The counters are not a partition. A message with a field of its own type that
// also sits in a larger cycle is both self and mutually recursive, and every
// recursive message is also counted as containing recursion.
type RecursionStats struct {
	// Messages on a cycle: self recursive, mutually recursive, or both.
	M_RecursiveC uint64 `json:"message_count_recursive" parquet:"message_count_recursive"`
	// Messages with a field of their own type.
	M_SelfRecC uint64 `json:"message_count_self_recursive" parquet:"message_count_self_recursive"`
	// Messages that reach themselves only by way of another message.
	M_MutualRecC uint64 `json:"message_count_mutually_recursive" parquet:"message_count_mutually_recursive"`
	// Messages that can reach a recursive message, themselves included, and
	// so can nest to unbounded depth.
	M_ContainsRecC uint64 `json:"message_count_contains_recursive" parquet:"message_count_contains_recursive"`
	// Cycles with at least one message declared in this file. A cycle is a
	// strongly connected component of the reference graph, so two messages
	// that reach each other by several distinct paths still count once.
	RecGroupC uint64 `json:"recursion_group_count" parquet:"recursion_group_count"`
	// Messages in the largest such cycle: 1 for a plain self reference.
	RecGroupMaxC uint64 `json:"recursion_group_max_size" parquet:"recursion_group_max_size"`
	// Cycles that pass through more than one file. Protobuf forbids
	// circular imports and a cross-file cycle would need one, so this is
	// expected to stay zero; it is reported as a check on that reasoning.
	RecGroupXFileC uint64 `json:"recursion_group_cross_file_count" parquet:"recursion_group_cross_file_count"`
}

type ProtoStats struct {
	MsgC          uint64 `json:"message_count_total" parquet:"message_count_total"`
	M_NestedEnumC uint64 `json:"message_count_nested_enum" parquet:"message_count_nested_enum"`
	// Includes the synthetic entry message of every map field; subtract
	// message_count_map_entry for the count of messages actually written
	// down in the file.
	M_NestedMsgC uint64 `json:"message_count_nested_msg" parquet:"message_count_nested_msg"`
	// Synthetic map entry messages, one per map field. The compiler sets a
	// map_entry option on them, which is how they are told apart from a
	// user-defined message that merely happens to be named FooEntry.
	//
	// These are counted in message_count_total and in
	// message_count_nested_msg as well, so that those two keep meaning what
	// they meant before this counter existed. Subtract this to correct
	// them. Each entry also contributes its own key and value fields to
	// field_count_total and to the per-type field counters, so the
	// correction there is twice this number.
	M_MapEntryC  uint64 `json:"message_count_map_entry" parquet:"message_count_map_entry"`
	M_ReservedRC uint64 `json:"message_count_reserved_range" parquet:"message_count_reserved_range"`
	M_ReservedNC uint64 `json:"message_count_reserved_name" parquet:"message_count_reserved_name"`
	FieldC       uint64 `json:"field_count_total" parquet:"field_count_total"`
	F_DoubleC    uint64 `json:"field_count_double" parquet:"field_count_double"`
	F_FloatC     uint64 `json:"field_count_float" parquet:"field_count_float"`
	F_Int64C     uint64 `json:"field_count_int64" parquet:"field_count_int64"`
	F_Uint64C    uint64 `json:"field_count_uint64" parquet:"field_count_uint64"`
	F_Int32C     uint64 `json:"field_count_int32" parquet:"field_count_int32"`
	F_Fixed64C   uint64 `json:"field_count_fixed64" parquet:"field_count_fixed64"`
	F_Fixed32C   uint64 `json:"field_count_fixed32" parquet:"field_count_fixed32"`
	F_BoolC      uint64 `json:"field_count_bool" parquet:"field_count_bool"`
	F_StringC    uint64 `json:"field_count_string" parquet:"field_count_string"`
	F_MessageC   uint64 `json:"field_count_message" parquet:"field_count_message"`
	F_BytesC     uint64 `json:"field_count_bytes" parquet:"field_count_bytes"`
	F_Uint32C    uint64 `json:"field_count_uint32" parquet:"field_count_uint32"`
	F_EnumC      uint64 `json:"field_count_enum" parquet:"field_count_enum"`
	F_Sfixed64C  uint64 `json:"field_count_sfixed64" parquet:"field_count_sfixed64"`
	F_Sfixed32C  uint64 `json:"field_count_sfixed32" parquet:"field_count_sfixed32"`
	F_Sint64C    uint64 `json:"field_count_sint64" parquet:"field_count_sint64"`
	F_Sint32C    uint64 `json:"field_count_sint32" parquet:"field_count_sint32"`
	F_OneofC     uint64 `json:"field_count_oneof" parquet:"field_count_oneof"`
	F_ImpC       uint64 `json:"field_count_implicit" parquet:"field_count_implicit"`
	F_OptC       uint64 `json:"field_count_optional" parquet:"field_count_optional"`
	// All map fields will be counted here
	F_RepC uint64 `json:"field_count_repeated" parquet:"field_count_repeated"`
	// Map fields. A map compiles to a repeated field of its synthetic entry
	// message, so these are also counted in field_count_repeated and in
	// field_count_message.
	F_MapC       uint64 `json:"field_count_map" parquet:"field_count_map"`
	EnumC        uint64 `json:"enum_count_total" parquet:"enum_count_total"`
	E_EnumC      uint64 `json:"enum_count_value" parquet:"enum_count_value"`
	E_ReservedRC uint64 `json:"enum_count_reserved_range" parquet:"enum_count_reserved_range"`
	E_ReservedNC uint64 `json:"enum_count_reserved_name" parquet:"enum_count_reserved_name"`
	ServiceC     uint64 `json:"service_count_total" parquet:"service_count_total"`
	MethodC      uint64 `json:"method_count_total" parquet:"method_count_total"`
	Me_CStreamC  uint64 `json:"method_count_client_streaming" parquet:"method_count_client_streaming"`
	Me_SStreamC  uint64 `json:"method_count_server_streaming" parquet:"method_count_server_streaming"`
	RecursionStats
}

func stats_walker(s *ProtoStats, rec *desclib.Analysis) func(d protoreflect.Descriptor) error {
	return func(d protoreflect.Descriptor) error {
		switch t := d.(type) {
		case protoreflect.MessageDescriptor:
			s.MsgC += 1
			s.M_NestedEnumC += uint64(t.Enums().Len())
			s.M_NestedMsgC += uint64(t.Messages().Len())
			if t.ReservedNames().Len() > 0 {
				s.M_ReservedNC += 1
			}
			if t.ReservedRanges().Len() > 0 {
				s.M_ReservedRC += 1
			}
			if t.IsMapEntry() {
				s.M_MapEntryC += 1
			}
			// Map entries are synthetic and are not nodes of the
			// reference graph, so they classify as non-recursive
			// even when the map they implement is part of a cycle.
			if !t.IsMapEntry() {
				r := rec.Msg(t.FullName())
				if r.Recursive() {
					s.M_RecursiveC += 1
				}
				if r.Self {
					s.M_SelfRecC += 1
				}
				if r.Mutual {
					s.M_MutualRecC += 1
				}
				if r.Contains {
					s.M_ContainsRecC += 1
				}
			}
		case protoreflect.FieldDescriptor:
			s.FieldC += 1
			if t.IsMap() {
				s.F_MapC += 1
			}
			if t.HasOptionalKeyword() {
				s.F_OptC += 1
			} else if t.Cardinality() == protoreflect.Repeated {
				s.F_RepC += 1
			} else {
				s.F_ImpC += 1
			}
			switch t.Kind() {
			case protoreflect.DoubleKind:
				s.F_DoubleC += 1
			case protoreflect.FloatKind:
				s.F_FloatC += 1
			case protoreflect.Int64Kind:
				s.F_Int64C += 1
			case protoreflect.Uint64Kind:
				s.F_Uint64C += 1
			case protoreflect.Int32Kind:
				s.F_Int32C += 1
			case protoreflect.Fixed32Kind:
				s.F_Fixed32C += 1
			case protoreflect.Fixed64Kind:
				s.F_Fixed64C += 1
			case protoreflect.BoolKind:
				s.F_BoolC += 1
			case protoreflect.StringKind:
				s.F_StringC += 1
			case protoreflect.BytesKind:
				s.F_BytesC += 1
			case protoreflect.MessageKind:
				s.F_MessageC += 1
			case protoreflect.Uint32Kind:
				s.F_Uint32C += 1
			case protoreflect.EnumKind:
				s.F_EnumC += 1
			case protoreflect.Sfixed64Kind:
				s.F_Sfixed64C += 1
			case protoreflect.Sfixed32Kind:
				s.F_Sfixed32C += 1
			case protoreflect.Sint64Kind:
				s.F_Sint64C += 1
			case protoreflect.Sint32Kind:
				s.F_Sint32C += 1
			}
		case protoreflect.EnumDescriptor:
			s.EnumC += 1
			// Even if there are multiple reserved ranges,
			// just count this as "an enum which uses reserved fields"
			if t.ReservedRanges().Len() > 0 {
				s.E_ReservedRC += 1
			}
			if t.ReservedNames().Len() > 0 {
				s.E_ReservedNC += 1
			}
		case protoreflect.EnumValueDescriptor:
			s.E_EnumC += 1
		case protoreflect.OneofDescriptor:
			// Oneof fields with this prefix are *probably* implicit onesof..
			if !strings.HasPrefix(string(t.Name()), "_optional_") {
				s.FieldC += 1
				s.F_OneofC += 1
			}
		case protoreflect.ServiceDescriptor:
			s.ServiceC += 1
		case protoreflect.MethodDescriptor:
			s.MethodC += 1
			if t.IsStreamingClient() {
				s.Me_CStreamC += 1
			}
			if t.IsStreamingServer() {
				s.Me_SStreamC += 1
			}
		default:
			// Never on stdout: that is where the JSON goes, and a
			// stray line in the middle of it would take down a
			// caller reading the statistics rather than one file.
			fmt.Fprintf(os.Stderr, "Unknown Descriptor Type: %T -> %+v\n\n", t, t)
		}
		return nil
	}
}

// addGroups counts the cycles that touch one file. A cycle is attributed to
// every file declaring one of its messages, so a cross-file cycle is counted
// once in each of them.
func (s *RecursionStats) addGroups(rec *desclib.Analysis, path string) {
	for _, g := range rec.Groups {
		if !slices.Contains(g.Files, path) {
			continue
		}
		s.RecGroupC += 1
		s.RecGroupMaxC = max(s.RecGroupMaxC, uint64(len(g.Members)))
		if g.CrossFile() {
			s.RecGroupXFileC += 1
		}
	}
}

// StatsResult is the summary of a set of files, plus whichever of them could
// not be compiled.
type StatsResult struct {
	Files  map[string]ProtoStats
	Errors map[string]string
}

// AnalyzeStats summarizes each of the given files. Import paths play the role
// of protoc's -I.
//
// Like the recursion report, the files are compiled together when they can be
// and one at a time when they cannot, so that a repository carrying two copies
// of a schema, or one file that does not compile, still yields a summary of
// everything else. This is what makes summarizing a whole repository in one
// invocation possible.
func AnalyzeStats(files []string, importPaths []string) StatsResult {
	// Files are reported under the paths they were asked about, not the
	// names the compiler gives them, so that a caller passing paths from
	// `find` together with an import path can still find its own files in
	// the answer.
	names := desclib.Canonicalize(files, importPaths)
	result := StatsResult{Files: make(map[string]ProtoStats, len(names.Compile))}
	for arg, why := range names.Excluded {
		result.fail(arg, why)
	}

	if fds, err := desclib.CompileProtos(names.Compile, importPaths...); err == nil {
		result.add(desclib.ToFileDescriptors(fds), names)
		return result
	}

	compiled, errs := desclib.CompileEach(names.Compile, importPaths...)
	for _, e := range errs {
		result.fail(names.Arg(e.Path), e.Err.Error())
	}
	for _, fd := range desclib.ToFileDescriptors(compiled) {
		result.add([]protoreflect.FileDescriptor{fd}, names)
	}
	return result
}

// fail records one file that produced no statistics.
func (r *StatsResult) fail(path, why string) {
	if r.Errors == nil {
		r.Errors = make(map[string]string)
	}
	r.Errors[path] = why
}

// add folds one compilation into the result.
func (r *StatsResult) add(fds []protoreflect.FileDescriptor, names desclib.Names) {
	// Recursion is a property of the whole reference graph rather than of a
	// single descriptor, so it is analyzed once, across every file given and
	// everything they import, before the per-file walk consults it.
	rec := desclib.AnalyzeRecursion(desclib.BuildRefGraph(fds))

	for _, fd := range fds {
		s := ProtoStats{}
		walk.Descriptors(fd, stats_walker(&s, rec))
		s.RecursionStats.addGroups(rec, fd.Path())
		r.Files[names.Arg(fd.Path())] = s
	}
}

// ComputeStats renders the summary as JSON, keyed by file. Files that did not
// compile are absent; AnalyzeStats reports them.
func ComputeStats(files []string, importPaths ...string) []byte {
	stats := AnalyzeStats(files, importPaths).Files

	s_json, err := json.Marshal(stats)
	if err != nil {
		log.Fatalf("Cannot encode statistics into JSON: %v\n", err)
	}
	return s_json
}
