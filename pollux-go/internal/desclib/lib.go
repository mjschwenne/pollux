package desclib

import (
	"context"
	"fmt"
	"iter"
	"reflect"

	"github.com/bufbuild/protocompile"
	"github.com/bufbuild/protocompile/linker"
	"github.com/bufbuild/protocompile/walk"
	"github.com/xlab/treeprint"
	"google.golang.org/protobuf/reflect/protodesc"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/types/descriptorpb"
)

func CompileProtos(files []string) (linker.Files, error) {
	ctx := context.Background()
	compiler := protocompile.Compiler{
		Resolver: protocompile.WithStandardImports(&protocompile.SourceResolver{}),
	}

	return compiler.Compile(ctx, files...)
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

func EnumIter(file protoreflect.FileDescriptor) iter.Seq[protoreflect.EnumDescriptor] {
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
