package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"log"
	"os"
	"sort"
	"strings"
)

// TypeCategory represents a category of types
type TypeCategory int

const (
	CategoryBasic TypeCategory = iota
	CategoryStruct
	CategoryPointer
	CategorySlice
	CategoryArray
	CategoryMap
	CategoryChan
	CategoryFunc
	CategoryInterface
	CategoryNamed
	CategoryUnsafePointer
)

func (tc TypeCategory) String() string {
	switch tc {
	case CategoryBasic:
		return "Basic"
	case CategoryStruct:
		return "Struct"
	case CategoryPointer:
		return "Pointer"
	case CategorySlice:
		return "Slice"
	case CategoryArray:
		return "Array"
	case CategoryMap:
		return "Map"
	case CategoryChan:
		return "Chan"
	case CategoryFunc:
		return "Func"
	case CategoryInterface:
		return "Interface"
	case CategoryNamed:
		return "Named"
	case CategoryUnsafePointer:
		return "UnsafePointer"
	default:
		return "Unknown"
	}
}

// FieldTypeInfo holds information about a field's type
type FieldTypeInfo struct {
	StructName     string
	FieldName      string
	TypeString     string
	Category       TypeCategory
	UnderlyingType string
	IsEmbedded     bool
}

// TypeStats holds statistics about type distribution
type TypeStats struct {
	Total            int
	ByCategory       map[TypeCategory]int
	ByUnderlyingType map[string]int
	Fields           []FieldTypeInfo
}

func main() {
	var (
		pkgPath   = flag.String("pkg", "./testdata/json", "Package path to analyze")
		verbose   = flag.Bool("v", false, "Verbose output showing all fields")
		showBasic = flag.Bool("basic", false, "Show basic type breakdown")
	)
	flag.Parse()

	// Analyze the package
	stats, err := analyzePackage(*pkgPath)
	if err != nil {
		log.Fatalf("Error analyzing package: %v", err)
	}

	// Print results
	printStats(stats, *verbose, *showBasic)
}

// analyzePackage parses and type-checks a Go package
func analyzePackage(pkgPath string) (*TypeStats, error) {
	// Create a file set
	fset := token.NewFileSet()

	// Parse all Go files in the directory
	pkgs, err := parser.ParseDir(fset, pkgPath, func(fi os.FileInfo) bool {
		return !strings.HasSuffix(fi.Name(), "_test.go")
	}, 0)
	if err != nil {
		return nil, fmt.Errorf("failed to parse directory: %w", err)
	}

	stats := &TypeStats{
		ByCategory:       make(map[TypeCategory]int),
		ByUnderlyingType: make(map[string]int),
		Fields:           []FieldTypeInfo{},
	}

	// Process each package
	for pkgName, pkg := range pkgs {
		// Collect all files
		var files []*ast.File
		for _, f := range pkg.Files {
			files = append(files, f)
		}

		// Create type-checker configuration
		conf := types.Config{
			Importer: importer.ForCompiler(fset, "source", nil),
			Error: func(err error) {
				// Ignore errors for now - we want to be permissive
				// Some imports might not resolve but we can still analyze what we can
			},
		}

		// Type-check the package
		info := &types.Info{
			Types: make(map[ast.Expr]types.TypeAndValue),
			Defs:  make(map[*ast.Ident]types.Object),
			Uses:  make(map[*ast.Ident]types.Object),
		}

		typedPkg, err := conf.Check(pkgName, fset, files, info)
		if err != nil {
			// Don't fail completely on type errors, just warn
			log.Printf("Warning: type checking errors (continuing anyway): %v", err)
		}

		if typedPkg != nil {
			// Analyze all structs in the package
			scope := typedPkg.Scope()
			for _, name := range scope.Names() {
				obj := scope.Lookup(name)
				if obj == nil {
					continue
				}

				// Check if this is a type definition
				typeName, ok := obj.(*types.TypeName)
				if !ok {
					continue
				}

				// Check if the underlying type is a struct
				if structType, ok := typeName.Type().Underlying().(*types.Struct); ok {
					analyzeStruct(name, structType, stats)
				}
			}
		}
	}

	return stats, nil
}

// analyzeStruct analyzes all fields in a struct
func analyzeStruct(structName string, structType *types.Struct, stats *TypeStats) {
	for i := 0; i < structType.NumFields(); i++ {
		field := structType.Field(i)
		fieldType := field.Type()

		// Determine the underlying type
		underlyingType := fieldType.Underlying().String()
		category := categorizeType(fieldType)

		fieldInfo := FieldTypeInfo{
			StructName:     structName,
			FieldName:      field.Name(),
			TypeString:     fieldType.String(),
			UnderlyingType: underlyingType,
			Category:       category,
			IsEmbedded:     field.Embedded(),
		}

		stats.Fields = append(stats.Fields, fieldInfo)
		stats.Total++
		stats.ByCategory[category]++
		stats.ByUnderlyingType[underlyingType]++
	}
}

// categorizeType determines the category of a type
func categorizeType(t types.Type) TypeCategory {
	underlying := t.Underlying()

	switch u := underlying.(type) {
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return CategoryUnsafePointer
		}
		return CategoryBasic
	case *types.Struct:
		return CategoryStruct
	case *types.Pointer:
		return CategoryPointer
	case *types.Slice:
		return CategorySlice
	case *types.Array:
		return CategoryArray
	case *types.Map:
		return CategoryMap
	case *types.Chan:
		return CategoryChan
	case *types.Signature:
		return CategoryFunc
	case *types.Interface:
		return CategoryInterface
	}

	// Check if it's a named type
	if _, ok := t.(*types.Named); ok {
		return CategoryNamed
	}

	return CategoryNamed
}

// printStats displays the statistics
func printStats(stats *TypeStats, verbose bool, showBasic bool) {
	fmt.Println("=== Struct Field Type Distribution ===")
	fmt.Printf("\nTotal fields analyzed: %d\n", stats.Total)

	// Print category distribution
	fmt.Println("\n--- By Category ---")

	// Sort categories by count
	type categoryCount struct {
		category TypeCategory
		count    int
	}
	var categories []categoryCount
	for cat, count := range stats.ByCategory {
		categories = append(categories, categoryCount{cat, count})
	}
	sort.Slice(categories, func(i, j int) bool {
		return categories[i].count > categories[j].count
	})

	for _, cc := range categories {
		percentage := float64(cc.count) / float64(stats.Total) * 100
		fmt.Printf("  %-15s: %4d (%.1f%%)\n", cc.category, cc.count, percentage)
	}

	// Print underlying type distribution
	fmt.Println("\n--- By Underlying Type ---")

	type typeCount struct {
		typeName string
		count    int
	}
	var types []typeCount
	for typeName, count := range stats.ByUnderlyingType {
		types = append(types, typeCount{typeName, count})
	}
	sort.Slice(types, func(i, j int) bool {
		return types[i].count > types[j].count
	})

	// Show top 20 most common types
	limit := 20
	if len(types) < limit {
		limit = len(types)
	}
	for _, tc := range types[:limit] {
		percentage := float64(tc.count) / float64(stats.Total) * 100
		fmt.Printf("  %-30s: %4d (%.1f%%)\n", tc.typeName, tc.count, percentage)
	}
	if len(types) > limit {
		fmt.Printf("  ... and %d more types\n", len(types)-limit)
	}

	// Show basic type breakdown if requested
	if showBasic {
		fmt.Println("\n--- Basic Type Breakdown ---")
		basicTypes := make(map[string]int)
		for _, field := range stats.Fields {
			if field.Category == CategoryBasic {
				basicTypes[field.UnderlyingType]++
			}
		}

		var basicList []typeCount
		for typeName, count := range basicTypes {
			basicList = append(basicList, typeCount{typeName, count})
		}
		sort.Slice(basicList, func(i, j int) bool {
			return basicList[i].count > basicList[j].count
		})

		for _, tc := range basicList {
			fmt.Printf("  %-20s: %4d\n", tc.typeName, tc.count)
		}
	}

	// Print individual fields if requested
	if verbose {
		fmt.Println("\n--- Individual Fields ---")
		for _, field := range stats.Fields {
			embedded := ""
			if field.IsEmbedded {
				embedded = " [embedded]"
			}
			fmt.Printf("  %s.%s: %s -> %s (%s)%s\n",
				field.StructName,
				field.FieldName,
				field.TypeString,
				field.UnderlyingType,
				field.Category,
				embedded)
		}
	}
}
