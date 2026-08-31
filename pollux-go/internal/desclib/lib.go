package desclib

import (
	"context"
	"fmt"
	"iter"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"

	"github.com/bufbuild/protocompile"
	"github.com/bufbuild/protocompile/linker"
	"github.com/bufbuild/protocompile/walk"
	"github.com/xlab/treeprint"

	"github.com/mjschwenne/pollux/internal/util"
	"google.golang.org/protobuf/reflect/protodesc"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/types/descriptorpb"
)

// CompileProtos compiles files into one linked scope. Import paths play the
// role of protoc's -I: an import is looked up under each of them in turn, and
// with none given, under the working directory.
//
// Everything compiled together shares a symbol scope, so a repository that
// vendors two copies of a schema -- googleapis carries google/rpc/code.proto
// both at the root and under preview/ -- cannot be compiled in one call. Use
// CompileEach for that.
func CompileProtos(files []string, importPaths ...string) (linker.Files, error) {
	ctx := context.Background()
	compiler := protocompile.Compiler{
		Resolver: protocompile.WithStandardImports(&protocompile.SourceResolver{
			ImportPaths: importPaths,
		}),
	}

	return compiler.Compile(ctx, files...)
}

// FileError is one file that could not be compiled.
type FileError struct {
	Path string
	Err  error
}

// CompileEach compiles every file in a scope of its own, so that neither a
// symbol defined twice across the set nor a single file that fails to compile
// can take down the rest. Each result is the requested file itself; its imports
// come with it, reachable through Imports().
//
// It returns what compiled and what did not, in the order the files were given.
func CompileEach(files []string, importPaths ...string) (linker.Files, []FileError) {
	var (
		ok   linker.Files
		errs []FileError
	)
	for _, f := range files {
		fds, err := CompileProtos([]string{f}, importPaths...)
		if err != nil {
			errs = append(errs, FileError{Path: f, Err: err})
			continue
		}
		ok = append(ok, fds...)
	}
	return ok, errs
}

// Names is how a set of file arguments maps onto the names the compiler knows
// them by. Import paths make the two differ, exactly as they do for protoc: a
// file found under an import path is named relative to it, and every import is
// resolved by searching the import paths in order, so the name is what the
// compiler deals in and the argument is what the caller wants to read back.
type Names struct {
	// Compile is what to hand the compiler: canonical names, sorted, with
	// duplicates removed.
	Compile []string
	// Given maps a compiler name back to the argument it came from.
	Given map[string]string
	// Excluded holds the arguments that cannot be compiled at all, each
	// mapped to the reason. There are two: a file under none of the import
	// paths cannot be opened, since the resolver only ever looks under
	// them, and a file whose every candidate name an earlier import path
	// answers with a different file cannot be named without compiling that
	// other file instead.
	Excluded map[string]string
}

// Arg is the argument a compiler name came from, or the name itself for a file
// that was never asked about -- an import pulled in to close the graph.
func (n Names) Arg(name string) string {
	if arg, ok := n.Given[name]; ok {
		return arg
	}
	return name
}

// Canonicalize names each file the way the compiler will, so that a caller can
// pass the output of `find` straight through and still get its own paths back.
//
// A file under several import paths has several candidate names, and the one
// picked is the first, in import path order, that the resolver answers with
// this very file: naming it by a later import path would silently compile
// whichever file the earlier one holds at that name. Files that do not exist
// are named by the first import path containing them, since there is nothing to
// resolve against; the compiler reports them.
func Canonicalize(files []string, importPaths []string) Names {
	n := Names{Given: make(map[string]string, len(files))}

	// With no import paths the resolver opens each path as given, so the
	// argument is already the name.
	if len(importPaths) == 0 {
		for _, f := range files {
			n.add(f, f)
		}
		slices.Sort(n.Compile)
		return n
	}

	roots := make([]string, 0, len(importPaths))
	for _, p := range importPaths {
		abs, err := filepath.Abs(p)
		if err != nil {
			continue
		}
		roots = append(roots, abs)
	}

	seen := statCache{}
	for _, f := range files {
		name, why := canonicalName(f, roots, seen)
		if why != "" {
			if n.Excluded == nil {
				n.Excluded = make(map[string]string)
			}
			n.Excluded[f] = why
			continue
		}
		n.add(name, f)
	}
	slices.Sort(n.Compile)
	return n
}

// add records one file, ignoring a name already claimed: the same file given
// twice, since two different files never canonicalize alike.
func (n *Names) add(name, arg string) {
	if _, ok := n.Given[name]; ok {
		return
	}
	n.Given[name] = arg
	n.Compile = append(n.Compile, name)
}

// canonicalName returns the name to compile f under, or the reason there is
// none.
func canonicalName(f string, roots []string, seen statCache) (name, why string) {
	abs, err := filepath.Abs(f)
	if err != nil {
		return f, ""
	}
	self := seen.stat(abs)

	var first, claimed string
	for _, root := range roots {
		rel, err := filepath.Rel(root, abs)
		// A file outside the root relativizes to something starting
		// with "..", which is not an import name.
		if err != nil || rel == ".." || strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
			continue
		}
		candidate := filepath.ToSlash(rel)
		if first == "" {
			first = candidate
		}
		if self == nil {
			// Nothing to resolve against, so take the first name
			// and let the compiler report the missing file.
			return candidate, ""
		}
		// Whichever import path answers this name first is the file
		// that would be compiled under it.
		for _, other := range roots {
			held := seen.stat(filepath.Join(other, candidate))
			if held == nil {
				continue
			}
			if os.SameFile(held, self) {
				return candidate, ""
			}
			if claimed == "" {
				claimed = filepath.Join(other, candidate)
			}
			break
		}
	}

	if first == "" {
		return "", "outside every import path"
	}
	return "", fmt.Sprintf("no name of its own: %s is %s under the import paths given", first, claimed)
}

// statCache remembers what is on disk, since canonicalizing a repository asks
// about the same directories over and over. A missing file is remembered as a
// nil FileInfo.
type statCache map[string]os.FileInfo

func (c statCache) stat(path string) os.FileInfo {
	if fi, ok := c[path]; ok {
		return fi
	}
	fi, err := os.Stat(path)
	if err != nil {
		fi = nil
	}
	c[path] = fi
	return fi
}

// Helper function to help with Go's type inference
func ToDescProto(fd linker.File) *descriptorpb.FileDescriptorProto {
	return protodesc.ToFileDescriptorProto(fd)
}

func MsgIter(file protoreflect.FileDescriptor) iter.Seq[protoreflect.MessageDescriptor] {
	return func(yield func(protoreflect.MessageDescriptor) bool) {
		for i := range file.Messages().Len() {
			if !yield(file.Messages().Get(i)) {
				return
			}
		}
	}
}

func NestedMsgIter(file protoreflect.MessageDescriptor) iter.Seq[protoreflect.MessageDescriptor] {
	return func(yield func(protoreflect.MessageDescriptor) bool) {
		for i := range file.Messages().Len() {
			if !yield(file.Messages().Get(i)) {
				return
			}
		}
	}
}

func EnumIter(file protoreflect.FileDescriptor) iter.Seq[protoreflect.EnumDescriptor] {
	return func(yield func(protoreflect.EnumDescriptor) bool) {
		for i := range file.Enums().Len() {
			if !yield(file.Enums().Get(i)) {
				return
			}
		}
	}
}

func NestedEnumIter(file protoreflect.MessageDescriptor) iter.Seq[protoreflect.EnumDescriptor] {
	return func(yield func(protoreflect.EnumDescriptor) bool) {
		for i := range file.Enums().Len() {
			if !yield(file.Enums().Get(i)) {
				return
			}
		}
	}
}

func FieldIter(msg protoreflect.MessageDescriptor) iter.Seq[protoreflect.FieldDescriptor] {
	return func(yield func(protoreflect.FieldDescriptor) bool) {
		for i := range msg.Fields().Len() {
			if !yield(msg.Fields().Get(i)) {
				return
			}
		}
	}
}

func ValueIter(enum protoreflect.EnumDescriptor) iter.Seq[protoreflect.EnumValueDescriptor] {
	return func(yield func(protoreflect.EnumValueDescriptor) bool) {
		for i := range enum.Values().Len() {
			if !yield(enum.Values().Get(i)) {
				return
			}
		}
	}
}

func Search(desc protoreflect.Descriptor, query []protoreflect.Descriptor) *protoreflect.Descriptor {
	next := query[len(query)-1]
	switch n := next.(type) {
	case protoreflect.MessageDescriptor:
		if p, ok := desc.(protoreflect.MessageDescriptor); ok {
			reflect.DeepEqual(n, p)
		} else {
			return nil
		}
	}
	return nil
}

type tree struct {
	root  treeprint.Tree
	trace []treeprint.Tree
}

func tree_walker(t *tree) (func(d protoreflect.Descriptor) error, func(d protoreflect.Descriptor) error) {
	enter := func(d protoreflect.Descriptor) error {
		switch p := d.(type) {
		case protoreflect.MessageDescriptor:
			end := len(t.trace) - 1
			m := t.trace[end].AddMetaBranch("MSG", p.Name())
			t.trace = append(t.trace, m)
		case protoreflect.FieldDescriptor:
			end := len(t.trace) - 1
			var ty string
			if p.Kind() == protoreflect.MessageKind {
				ty = fmt.Sprintf("message (%s) %v", p.Message().Name(), p.Number())
			} else {
				ty = fmt.Sprintf("%v %v", p.Kind(), p.Number())
			}
			t.trace[end].AddMetaNode(ty, p.Name())
		case protoreflect.EnumDescriptor:
			end := len(t.trace) - 1
			e := t.trace[end].AddMetaBranch("ENUM", p.Name())
			t.trace = append(t.trace, e)
		case protoreflect.EnumValueDescriptor:
			end := len(t.trace) - 1
			t.trace[end].AddNode(p.Name())
		}
		return nil
	}
	exit := func(d protoreflect.Descriptor) error {
		switch d.(type) {
		case protoreflect.MessageDescriptor:
			t.trace = t.trace[:len(t.trace)-1]
		case protoreflect.EnumDescriptor:
			t.trace = t.trace[:len(t.trace)-1]
		}
		return nil
	}
	return enter, exit
}

func PrintFileDesc(d linker.File) {
	t := treeprint.NewWithRoot(d.Path())
	tree := &tree{root: t, trace: []treeprint.Tree{t}}
	enter, exit := tree_walker(tree)
	walk.DescriptorsEnterAndExit(d, enter, exit)

	fmt.Print(tree.root)
}

func ExtensionIter(msg protoreflect.MessageDescriptor) iter.Seq[protoreflect.ExtensionDescriptor] {
	return func(yield func(protoreflect.ExtensionDescriptor) bool) {
		for i := range msg.Extensions().Len() {
			if !yield(msg.Extensions().Get(i)) {
				return
			}
		}
	}
}

func FileExtensionIter(file protoreflect.FileDescriptor) iter.Seq[protoreflect.ExtensionDescriptor] {
	return func(yield func(protoreflect.ExtensionDescriptor) bool) {
		for i := range file.Extensions().Len() {
			if !yield(file.Extensions().Get(i)) {
				return
			}
		}
	}
}

// ToFileDescriptors forgets the linker's extra structure, for the analyses that
// only need the reflective descriptor interface.
func ToFileDescriptors(files linker.Files) []protoreflect.FileDescriptor {
	return util.Map(files, func(f linker.File) protoreflect.FileDescriptor {
		return f
	})
}
