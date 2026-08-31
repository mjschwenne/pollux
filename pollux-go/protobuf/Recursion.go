package pollux_proto

import (
	"encoding/json"
	"fmt"
	"log"
	"maps"
	"slices"
	"strings"

	"google.golang.org/protobuf/reflect/protoreflect"

	"github.com/mjschwenne/pollux/internal/desclib"
	"github.com/mjschwenne/pollux/internal/util"
)

// RecursionEdgeReport is one field that takes part in a cycle.
type RecursionEdgeReport struct {
	From string `json:"from" parquet:"from"`
	To   string `json:"to" parquet:"to"`
	// Field is the fully qualified name of the field creating the
	// reference, which for an extension is not inside From.
	Field  string `json:"field" parquet:"field"`
	Number int32  `json:"number" parquet:"number"`
	// Label is "singular", "repeated" or "map", prefixed with "extension "
	// when the field is an extension of From rather than one of its fields.
	Label     string `json:"label" parquet:"label"`
	Map       bool   `json:"map" parquet:"map"`
	Repeated  bool   `json:"repeated" parquet:"repeated"`
	Extension bool   `json:"extension" parquet:"extension"`
}

// RecursionGroupReport is one cycle: a strongly connected component of the
// message reference graph with at least one edge inside it.
type RecursionGroupReport struct {
	Size int `json:"size" parquet:"size"`
	// Self is set when some member has a field of its own type.
	Self bool `json:"self_recursive" parquet:"self_recursive"`
	// Mutual is set when the cycle runs through several messages.
	Mutual    bool     `json:"mutually_recursive" parquet:"mutually_recursive"`
	CrossFile bool     `json:"cross_file" parquet:"cross_file"`
	Messages  []string `json:"messages" parquet:"messages"`
	Files     []string `json:"files" parquet:"files"`
	// Edges are the references between members of the cycle. There can be
	// more of them than there are members: a component collects every path
	// between its messages, not one cycle.
	Edges []RecursionEdgeReport `json:"edges" parquet:"edges"`
}

// RecursionTotals aggregates over every file the analysis was asked about.
// Unlike the per-file counters, a cycle is counted once here rather than once
// per file declaring one of its messages.
type RecursionTotals struct {
	FileC uint64 `json:"file_count" parquet:"file_count"`
	// MsgC counts messages declared in the analyzed files, excluding
	// synthetic map entries, so it is the denominator for the counters
	// below. It is smaller than the stats command's message_count_total,
	// which does count map entries.
	MsgC uint64 `json:"message_count_total" parquet:"message_count_total"`
	RecursionStats
}

// RecursionReport is the detailed answer to "which messages are recursive, and
// through which fields". The per-file counters match the recursion keys of the
// stats command.
type RecursionReport struct {
	Totals RecursionTotals           `json:"totals" parquet:"totals"`
	Files  map[string]RecursionStats `json:"files" parquet:"files"`
	Groups []RecursionGroupReport    `json:"groups" parquet:"groups"`
	// Errors holds the files that could not be compiled, by path. Their
	// absence from Files is the only trace they leave in the counters.
	Errors map[string]string `json:"errors,omitempty" parquet:"errors"`
}

// AnalyzeRecursion compiles the given files and classifies the recursion among
// the messages they declare. Imported files take part in the analysis, since a
// message can reach recursion that lives in one of them, but are not reported
// on themselves. Import paths play the role of protoc's -I.
//
// The files are compiled together when they can be, and one at a time when they
// cannot. Compiling together is much faster, since a shared import is parsed
// once instead of once per file, but it puts everything in a single symbol
// scope, which a repository holding two copies of a schema cannot survive.
// Falling back keeps such a repository analyzable, and stops one file that does
// not compile from taking down the whole run; the files that fail are reported
// rather than skipped silently.
//
// Analyzing a file on its own gives it the same counters as analyzing it in a
// batch. A file's own imports come with it either way, and that is all its
// counters depend on: a cycle cannot reach outside the file it is declared in,
// so unrelated files in the batch contribute nothing to it.
func AnalyzeRecursion(files []string, importPaths []string) RecursionReport {
	// Naming the files the way the compiler does also makes duplicates
	// visible, and a file given twice would otherwise be compiled twice and
	// counted twice in the fallback below. The report keys are the paths as
	// given, since those are what the caller can join against.
	names := desclib.Canonicalize(files, importPaths)
	report := RecursionReport{Files: make(map[string]RecursionStats, len(names.Compile))}
	for arg, why := range names.Excluded {
		report.fail(arg, why)
	}

	if fds, err := desclib.CompileProtos(names.Compile, importPaths...); err == nil {
		report.add(desclib.ToFileDescriptors(fds), names)
		return report
	}

	compiled, errs := desclib.CompileEach(names.Compile, importPaths...)
	for _, e := range errs {
		report.fail(names.Arg(e.Path), e.Err.Error())
	}
	for _, fd := range desclib.ToFileDescriptors(compiled) {
		report.add([]protoreflect.FileDescriptor{fd}, names)
	}
	return report
}

// fail records one file that could not be analyzed.
func (r *RecursionReport) fail(path, why string) {
	if r.Errors == nil {
		r.Errors = make(map[string]string)
	}
	r.Errors[path] = why
}

// add folds one compilation into the report. Only messages declared in the
// given files are counted; the files they import are in the graph so that
// reachability is right, but are not reported on.
func (r *RecursionReport) add(fds []protoreflect.FileDescriptor, names desclib.Names) {
	rec := desclib.AnalyzeRecursion(desclib.BuildRefGraph(fds))

	paths := make([]string, 0, len(fds))
	for _, fd := range fds {
		paths = append(paths, fd.Path())
	}
	r.Totals.FileC += uint64(len(paths))

	for _, name := range rec.Graph.Names() {
		m := rec.Msg(name)
		if !slices.Contains(paths, m.File) {
			continue
		}
		r.Totals.MsgC += 1
		s := r.Files[names.Arg(m.File)]
		count(&s, m)
		count(&r.Totals.RecursionStats, m)
		r.Files[names.Arg(m.File)] = s
	}
	// A file with no recursion still deserves a row, so that a caller can
	// tell "analyzed, none found" from "not analyzed".
	for _, p := range paths {
		if _, ok := r.Files[names.Arg(p)]; !ok {
			r.Files[names.Arg(p)] = RecursionStats{}
		}
	}

	for _, g := range rec.Groups {
		if !slices.ContainsFunc(g.Files, func(f string) bool { return slices.Contains(paths, f) }) {
			continue
		}
		r.Groups = append(r.Groups, groupReport(g, names))

		r.Totals.RecGroupC += 1
		r.Totals.RecGroupMaxC = max(r.Totals.RecGroupMaxC, uint64(len(g.Members)))
		if g.CrossFile() {
			r.Totals.RecGroupXFileC += 1
		}
	}
	for _, p := range paths {
		// The cycles carry compiler paths, so the lookup is by those
		// and only the report key is the caller's.
		s := r.Files[names.Arg(p)]
		s.addGroups(rec, p)
		r.Files[names.Arg(p)] = s
	}
}

func count(s *RecursionStats, m desclib.MsgRecursion) {
	if m.Recursive() {
		s.M_RecursiveC += 1
	}
	if m.Self {
		s.M_SelfRecC += 1
	}
	if m.Mutual {
		s.M_MutualRecC += 1
	}
	if m.Contains {
		s.M_ContainsRecC += 1
	}
}

func groupReport(g desclib.RecursionGroup, names desclib.Names) RecursionGroupReport {
	r := RecursionGroupReport{
		Size:      len(g.Members),
		Self:      g.Self,
		Mutual:    len(g.Members) > 1,
		CrossFile: g.CrossFile(),
		// A cycle can live in a file that was never asked about, in
		// which case there is no caller path to name it by and the
		// compiler's stands.
		Files: util.Map(g.Files, names.Arg),
	}
	for _, m := range g.Members {
		r.Messages = append(r.Messages, string(m))
	}
	for _, e := range g.Edges {
		r.Edges = append(r.Edges, RecursionEdgeReport{
			From:      string(e.From),
			To:        string(e.To),
			Field:     string(e.Field.FullName()),
			Number:    int32(e.Field.Number()),
			Label:     edgeLabel(e),
			Map:       e.ViaMap,
			Repeated:  e.Repeated,
			Extension: e.Extension,
		})
	}
	slices.SortFunc(r.Edges, func(a, b RecursionEdgeReport) int {
		if a.From != b.From {
			return strings.Compare(a.From, b.From)
		}
		return int(a.Number - b.Number)
	})
	return r
}

func edgeLabel(e desclib.RefEdge) string {
	var label string
	switch {
	case e.ViaMap:
		label = "map"
	case e.Repeated:
		label = "repeated"
	default:
		label = "singular"
	}
	if e.Extension {
		return "extension " + label
	}
	return label
}

// JSON renders the report.
func (r RecursionReport) JSON() []byte {
	out, err := json.Marshal(r)
	if err != nil {
		log.Fatalf("Cannot encode recursion report into JSON: %v\n", err)
	}
	return out
}

// Text renders the report for a human reader.
func (r RecursionReport) Text() string {
	var b strings.Builder
	t := r.Totals
	fmt.Fprintf(&b, "%d file(s), %d message(s)\n", t.FileC, t.MsgC)
	fmt.Fprintf(&b, "  recursive:            %d (%d self, %d mutual)\n",
		t.M_RecursiveC, t.M_SelfRecC, t.M_MutualRecC)
	fmt.Fprintf(&b, "  contains recursion:   %d\n", t.M_ContainsRecC)
	fmt.Fprintf(&b, "  cycles:               %d (largest %d, %d cross-file)\n",
		t.RecGroupC, t.RecGroupMaxC, t.RecGroupXFileC)
	if len(r.Errors) > 0 {
		fmt.Fprintf(&b, "  did not compile:      %d\n", len(r.Errors))
	}

	if len(r.Groups) == 0 {
		fmt.Fprintf(&b, "\nno recursive messages\n")
	}
	for i, g := range r.Groups {
		kind := "self recursive"
		if g.Mutual {
			kind = fmt.Sprintf("mutually recursive, %d messages", g.Size)
		}
		if g.CrossFile {
			kind += ", cross-file"
		}
		fmt.Fprintf(&b, "\ncycle %d (%s)\n", i+1, kind)
		for _, f := range g.Files {
			fmt.Fprintf(&b, "  file %s\n", f)
		}
		for _, m := range g.Messages {
			fmt.Fprintf(&b, "  msg  %s\n", m)
		}
		for _, e := range g.Edges {
			fmt.Fprintf(&b, "       %s --%s %d--> %s\n",
				e.From, e.Label, e.Number, e.To)
		}
	}

	if len(r.Errors) > 0 {
		fmt.Fprintf(&b, "\n%d file(s) did not compile:\n", len(r.Errors))
		for _, p := range slices.Sorted(maps.Keys(r.Errors)) {
			fmt.Fprintf(&b, "  %s: %s\n", p, r.Errors[p])
		}
	}
	return b.String()
}
