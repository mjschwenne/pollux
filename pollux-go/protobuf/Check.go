package pollux_proto

import (
	"context"
	"fmt"
	"log"
	"os"

	sitter "github.com/smacker/go-tree-sitter"
	proto "github.com/smacker/go-tree-sitter/protobuf"
	"google.golang.org/protobuf/reflect/protoreflect"
)

func eq_walker(trace []protoreflect.Descriptor) (func(d protoreflect.Descriptor) error,
	func(d protoreflect.Descriptor) error) {
	enter := func(d protoreflect.Descriptor) error {
		return nil
	}
	exit := func(d protoreflect.Descriptor) error {
		return nil
	}
	return enter, exit
}

func Test(a string, b string) {
	parser := sitter.NewParser()
	parser.SetLanguage(proto.GetLanguage())

	a_byt, err := os.ReadFile(a)
	if err != nil {
		log.Fatalf("Error: %v\n", err)
	}

	a_tree, err := parser.ParseCtx(context.Background(), nil, a_byt)
	if err != nil {
		log.Fatalf("Error: %v\n", err)
	}
	fmt.Printf("a: %v\n", a_tree.RootNode())

	b_byt, err := os.ReadFile(b)
	if err != nil {
		log.Fatalf("Error: %v\n", err)
	}

	b_tree, err := parser.ParseCtx(context.Background(), nil, b_byt)
	if err != nil {
		log.Fatalf("Error: %v\n", err)
	}
	fmt.Printf("b: %v\n", b_tree.RootNode())
}
