package desclib

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"google.golang.org/protobuf/reflect/protoreflect"
)

// analyze compiles files from testdata/proto/recursion and classifies them.
// The compiler resolves imports relative to the working directory, so the test
// runs from the directory holding the files rather than naming them by path.
func analyze(t *testing.T, files ...string) *Analysis {
	t.Helper()
	t.Chdir("../../testdata/proto/recursion")
	return analyzeHere(t, files...)
}

// analyzeHere is analyze once the working directory is already set, for the
// tests that analyze more than once and so cannot chdir per call.
func analyzeHere(t *testing.T, files ...string) *Analysis {
	t.Helper()

	fds, err := CompileProtos(files)
	if err != nil {
		t.Fatalf("compiling %v: %v", files, err)
	}
	return AnalyzeRecursion(BuildRefGraph(ToFileDescriptors(fds)))
}

func TestClassification(t *testing.T) {
	a := analyze(t, "recursion.proto")

	tests := []struct {
		msg      protoreflect.FullName
		self     bool
		mutual   bool
		contains bool
	}{
		{msg: "rec.Tree", self: true, contains: true},
		{msg: "rec.MapNode", self: true, contains: true},
		{msg: "rec.Outer.Inner", self: true, contains: true},

		{msg: "rec.Expr", mutual: true, contains: true},
		{msg: "rec.Stmt", mutual: true, contains: true},
		{msg: "rec.A", mutual: true, contains: true},
		{msg: "rec.B", mutual: true, contains: true},
		{msg: "rec.C", mutual: true, contains: true},
		{msg: "rec.Value", mutual: true, contains: true},
		{msg: "rec.ValueList", mutual: true, contains: true},

		// Not on a cycle, but reaches one.
		{msg: "rec.Root", contains: true},
		{msg: "rec.Outer", contains: true},

		// A map with a scalar value is not a reference, and neither of
		// these reaches anything recursive.
		{msg: "rec.MapScalar"},
		{msg: "rec.Leaf"},
		{msg: "rec.Wrapper"},
	}

	for _, tt := range tests {
		m := a.Msg(tt.msg)
		if m.Self != tt.self || m.Mutual != tt.mutual || m.Contains != tt.contains {
			t.Errorf("%s: got self=%v mutual=%v contains=%v, want self=%v mutual=%v contains=%v",
				tt.msg, m.Self, m.Mutual, m.Contains, tt.self, tt.mutual, tt.contains)
		}
	}

	if len(tests) != len(a.Graph.Names()) {
		t.Errorf("graph has %d messages, the table covers %d",
			len(a.Graph.Names()), len(tests))
	}
}

func TestGroups(t *testing.T) {
	a := analyze(t, "recursion.proto")

	want := [][]protoreflect.FullName{
		{"rec.A", "rec.B", "rec.C"},
		{"rec.Expr", "rec.Stmt"},
		{"rec.MapNode"},
		{"rec.Outer.Inner"},
		{"rec.Tree"},
		{"rec.Value", "rec.ValueList"},
	}

	if len(a.Groups) != len(want) {
		t.Fatalf("got %d cycles, want %d", len(a.Groups), len(want))
	}
	for i, g := range a.Groups {
		if !slices.Equal(g.Members, want[i]) {
			t.Errorf("cycle %d: got %v, want %v", i, g.Members, want[i])
		}
		if g.CrossFile() {
			t.Errorf("cycle %d spans %v, but a cycle cannot cross files", i, g.Files)
		}
	}

	// Every recursive message points back at the cycle holding it.
	for name, m := range a.Msgs {
		if !m.Recursive() {
			if m.Group != -1 {
				t.Errorf("%s is not recursive but is in cycle %d", name, m.Group)
			}
			continue
		}
		if !slices.Contains(a.Groups[m.Group].Members, name) {
			t.Errorf("%s is not a member of its own cycle %d", name, m.Group)
		}
	}
}

// A map field compiles to a repeated synthetic entry message. Counting that
// entry would turn a self reference through a map into a two message cycle.
func TestMapEntryIsNotANode(t *testing.T) {
	a := analyze(t, "recursion.proto")

	if n := a.Graph.Node("rec.MapNode.ChildrenEntry"); n != nil {
		t.Errorf("map entry %s is in the graph", n.Name)
	}

	m := a.Msg("rec.MapNode")
	if !m.Self || m.Mutual {
		t.Errorf("rec.MapNode: got self=%v mutual=%v, want self=true mutual=false", m.Self, m.Mutual)
	}
	if got := a.Groups[m.Group].Members; len(got) != 1 {
		t.Errorf("rec.MapNode is in a cycle of %v, want just itself", got)
	}
}

// Recursion reached through an import is what makes following imports worth the
// trouble: Config is not on a cycle, but google.protobuf.Struct is.
func TestRecursionThroughImport(t *testing.T) {
	a := analyze(t, "imports.proto")

	if m := a.Msg("rec.Config"); m.Recursive() || !m.Contains {
		t.Errorf("rec.Config: got recursive=%v contains=%v, want recursive=false contains=true",
			m.Recursive(), m.Contains)
	}
	if m := a.Msg("rec.Plain"); m.Recursive() || m.Contains {
		t.Errorf("rec.Plain: got recursive=%v contains=%v, want both false",
			m.Recursive(), m.Contains)
	}
	if m := a.Msg("google.protobuf.Struct"); !m.Mutual {
		t.Error("google.protobuf.Struct should be mutually recursive")
	}
}

func TestGroupsAndExtensions(t *testing.T) {
	a := analyze(t, "groups.proto")

	// A proto2 group is an ordinary message type behind the scenes.
	for _, name := range []protoreflect.FullName{"rec2.GroupHolder", "rec2.GroupHolder.Nested"} {
		if m := a.Msg(name); !m.Mutual {
			t.Errorf("%s should be mutually recursive", name)
		}
	}

	// The extension is declared at file scope, but the reference it creates
	// belongs to the message it extends.
	if m := a.Msg("rec2.Extendable"); !m.Self {
		t.Error("rec2.Extendable should be self recursive through the extension that extends it")
	}
}

// Tarjan visits vertices in map order, so the analysis has to impose an order
// of its own for the reports built from it to be stable.
func TestDeterministicOrder(t *testing.T) {
	first := analyze(t, "recursion.proto")
	for range 5 {
		next := analyzeHere(t, "recursion.proto")
		if len(next.Groups) != len(first.Groups) {
			t.Fatalf("got %d cycles, want %d", len(next.Groups), len(first.Groups))
		}
		for i := range next.Groups {
			if !slices.Equal(next.Groups[i].Members, first.Groups[i].Members) {
				t.Fatalf("cycle %d: got %v, want %v",
					i, next.Groups[i].Members, first.Groups[i].Members)
			}
		}
	}
}

// Import paths turn a path on disk into the name the compiler resolves imports
// by, which is what lets a caller pass the output of `find` straight through.
func TestCanonicalize(t *testing.T) {
	root := t.TempDir()
	write := func(rel string) string {
		path := filepath.Join(root, filepath.FromSlash(rel))
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte("syntax = \"proto3\";\n"), 0o644); err != nil {
			t.Fatal(err)
		}
		return path
	}

	code := write("google/rpc/code.proto")
	preview := write("preview/google/rpc/code.proto")
	only := write("preview/google/rpc/preview_only.proto")

	// Two copies of one schema in sibling directories, each of which is an
	// import path of its own: the arrangement a repository that vendors a
	// second copy of a schema ends up with.
	vendored := write("vendor/a/dup.proto")
	shadowed := write("vendor/b/dup.proto")

	tests := []struct {
		name        string
		file        string
		importPaths []string
		want        string
		wantExcuse  string
	}{
		{
			name:        "relative to the import path",
			file:        code,
			importPaths: []string{root},
			want:        "google/rpc/code.proto",
		},
		{
			name: "named by the import path that answers to the name",
			file: only,
			// The file is under both, and only the second gives it
			// a name the resolver answers with this file.
			importPaths: []string{root, filepath.Join(root, "preview")},
			want:        "preview/google/rpc/preview_only.proto",
		},
		{
			name: "the earlier import path wins the shared name",
			file: code,
			// Both copies want to be google/rpc/code.proto, and the
			// resolver would hand out this one.
			importPaths: []string{root, filepath.Join(root, "preview")},
			want:        "google/rpc/code.proto",
		},
		{
			name: "the longer name is still a name",
			file: preview,
			// Not "google/rpc/code.proto", which is the other copy,
			// but naming it through the outer import path works.
			importPaths: []string{root, filepath.Join(root, "preview")},
			want:        "preview/google/rpc/code.proto",
		},
		{
			name:        "and its own import path first gives it the short one",
			file:        preview,
			importPaths: []string{filepath.Join(root, "preview"), root},
			want:        "google/rpc/code.proto",
		},
		{
			name: "a copy with no name of its own is left out",
			file: shadowed,
			// Its only name is dup.proto, and that is the other
			// copy: compiling it would silently measure that one.
			importPaths: []string{filepath.Join(root, "vendor", "a"), filepath.Join(root, "vendor", "b")},
			wantExcuse:  "is " + vendored,
		},
		{
			name:        "a file under no import path cannot be opened at all",
			file:        "elsewhere/thing.proto",
			importPaths: []string{root},
			wantExcuse:  "outside every import path",
		},
		{
			name: "no import paths at all",
			file: "google/rpc/code.proto",
			want: "google/rpc/code.proto",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := Canonicalize([]string{tt.file}, tt.importPaths)
			if tt.wantExcuse != "" {
				why, ok := got.Excluded[tt.file]
				if !ok {
					t.Fatalf("got %v, want it excluded", got.Compile)
				}
				if !strings.Contains(why, tt.wantExcuse) {
					t.Errorf("reason %q does not mention %q", why, tt.wantExcuse)
				}
				return
			}
			if len(got.Compile) != 1 || got.Compile[0] != tt.want {
				t.Fatalf("got %v, want [%s]", got.Compile, tt.want)
			}
			if arg := got.Arg(tt.want); arg != tt.file {
				t.Errorf("the name maps back to %s, want %s", arg, tt.file)
			}
		})
	}
}

// The same file twice is one file, and does not become two rows.
func TestCanonicalizeDuplicateArgument(t *testing.T) {
	got := Canonicalize([]string{"a.proto", "a.proto"}, nil)
	if len(got.Compile) != 1 {
		t.Errorf("got %v, want one name", got.Compile)
	}
}
