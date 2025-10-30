package main

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"log"
)

func main() {
	// Example source code with type aliases
	src := `
package example

type MyInt int
type MyString string

type Embedded struct {
	Value int
}

type Example struct {
	// Basic type
	Name string

	// Type alias - this will resolve to 'int'
	Count MyInt

	// Another alias
	Label MyString

	// Struct type
	Data Embedded

	// Pointer to struct
	Ptr *Embedded

	// Slice
	Items []MyInt

	// Map with alias
	Tags map[string]MyInt
}
`

	// Parse the source code
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "example.go", src, 0)
	if err != nil {
		log.Fatal(err)
	}

	// Configure the type checker
	conf := types.Config{
		Importer: importer.Default(),
	}

	// Info stores the resolved type information
	info := &types.Info{
		Types: make(map[ast.Expr]types.TypeAndValue),
		Defs:  make(map[*ast.Ident]types.Object),
	}

	// Type-check the package
	pkg, err := conf.Check("example", fset, []*ast.File{file}, info)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("=== Type Resolution Example ===\n")

	// Find the Example struct
	obj := pkg.Scope().Lookup("Example")
	if obj == nil {
		log.Fatal("Example struct not found")
	}

	typeName := obj.(*types.TypeName)
	structType := typeName.Type().Underlying().(*types.Struct)

	// Analyze each field
	fmt.Printf("Struct: %s\n\n", typeName.Name())
	fmt.Printf("%-15s %-20s %-20s %s\n", "Field", "Declared Type", "Underlying Type", "Resolved?")
	fmt.Println("-------------------------------------------------------------------")

	for i := 0; i < structType.NumFields(); i++ {
		field := structType.Field(i)
		fieldType := field.Type()
		underlyingType := fieldType.Underlying()

		declaredTypeStr := fieldType.String()
		underlyingTypeStr := underlyingType.String()

		// Check if type was resolved (different from declared)
		resolved := "No"
		if declaredTypeStr != underlyingTypeStr {
			resolved = "Yes ✓"
		}

		fmt.Printf("%-15s %-20s %-20s %s\n",
			field.Name(),
			declaredTypeStr,
			underlyingTypeStr,
			resolved)
	}

	fmt.Println("\n=== Type Categories ===\n")

	// Demonstrate type categorization
	for i := 0; i < structType.NumFields(); i++ {
		field := structType.Field(i)
		fieldType := field.Type()
		underlyingType := fieldType.Underlying()

		category := categorize(underlyingType)
		fmt.Printf("%-15s -> %s\n", field.Name(), category)
	}

	fmt.Println("\n=== Key Insight ===")
	fmt.Println("MyInt and MyString are type aliases that resolve to their underlying types.")
	fmt.Println("The go/types package automatically resolves these, unlike go/ast alone.")
}

// categorize determines the category of a type
func categorize(t types.Type) string {
	switch u := t.(type) {
	case *types.Basic:
		return fmt.Sprintf("Basic (%s)", u.Name())
	case *types.Struct:
		return "Struct"
	case *types.Pointer:
		elem := u.Elem()
		return fmt.Sprintf("Pointer to %s", categorize(elem))
	case *types.Slice:
		elem := u.Elem()
		return fmt.Sprintf("Slice of %s", categorize(elem))
	case *types.Map:
		key := u.Key()
		val := u.Elem()
		return fmt.Sprintf("Map[%s]%s", categorize(key), categorize(val))
	case *types.Array:
		return fmt.Sprintf("Array[%d]", u.Len())
	case *types.Chan:
		return "Channel"
	case *types.Interface:
		return "Interface"
	default:
		return "Other"
	}
}
