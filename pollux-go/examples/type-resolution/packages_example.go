package main

import (
	"fmt"
	"go/types"
	"log"

	"golang.org/x/tools/go/packages"
)

func main() {
	// Configure what information we need
	cfg := &packages.Config{
		Mode: packages.NeedTypes | packages.NeedTypesInfo | packages.NeedSyntax,
	}

	// Load the package - use "." for current directory or provide a path
	// Example: "." or "github.com/user/repo/pkg"
	// For this demo, we'll analyze the current directory
	pkgs, err := packages.Load(cfg, ".")
	if err != nil {
		log.Fatalf("Error loading packages: %v", err)
	}

	// Check for errors in the loaded packages
	if packages.PrintErrors(pkgs) > 0 {
		log.Println("Warning: Some packages had errors, continuing anyway...")
	}

	fmt.Println("=== Struct Field Analysis using go/packages ===\n")

	typeStats := make(map[string]int)
	categoryStats := make(map[string]int)

	// Process each package
	for _, pkg := range pkgs {
		fmt.Printf("Package: %s\n\n", pkg.Name)

		// Get the package scope
		scope := pkg.Types.Scope()

		// Iterate through all names in the package
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
			structType, ok := typeName.Type().Underlying().(*types.Struct)
			if !ok {
				continue
			}

			// Found a struct! Analyze its fields
			fmt.Printf("Struct: %s (%d fields)\n", name, structType.NumFields())
			fmt.Println("  Field                Type                 Underlying           Category")
			fmt.Println("  " + "─────────────────────────────────────────────────────────────────────────────")

			for i := 0; i < structType.NumFields(); i++ {
				field := structType.Field(i)
				fieldType := field.Type()
				underlyingType := fieldType.Underlying()

				// Categorize the type
				category := categorizeType(underlyingType)

				// Track statistics
				underlyingStr := underlyingType.String()
				typeStats[underlyingStr]++
				categoryStats[category]++

				// Format for display
				embeddedMarker := ""
				if field.Embedded() {
					embeddedMarker = " [embedded]"
				}

				fmt.Printf("  %-20s %-20s %-20s %s%s\n",
					field.Name(),
					truncate(fieldType.String(), 20),
					truncate(underlyingStr, 20),
					category,
					embeddedMarker)
			}
			fmt.Println()
		}
	}

	// Print statistics
	fmt.Println("=== Type Distribution ===\n")
	fmt.Println("By Category:")
	for cat, count := range categoryStats {
		fmt.Printf("  %-15s: %d\n", cat, count)
	}

	fmt.Println("\nBy Underlying Type (top 10):")
	topTypes := getTopN(typeStats, 10)
	for _, item := range topTypes {
		fmt.Printf("  %-30s: %d\n", item.key, item.count)
	}

	fmt.Println("\n=== Key Observations ===")
	fmt.Println("✓ Type aliases (like 'type MyInt int') are resolved to their underlying types")
	fmt.Println("✓ Named structs show both the name and the underlying structure")
	fmt.Println("✓ go/packages handles all imports and dependencies automatically")
	fmt.Println("✓ This approach works with Go modules without manual configuration")
}

// categorizeType returns a human-readable category for a type
func categorizeType(t types.Type) string {
	switch u := t.(type) {
	case *types.Basic:
		if u.Kind() == types.UnsafePointer {
			return "UnsafePointer"
		}
		return "Basic"
	case *types.Struct:
		return "Struct"
	case *types.Pointer:
		return "Pointer"
	case *types.Slice:
		return "Slice"
	case *types.Array:
		return "Array"
	case *types.Map:
		return "Map"
	case *types.Chan:
		return "Chan"
	case *types.Signature:
		return "Func"
	case *types.Interface:
		return "Interface"
	default:
		return "Other"
	}
}

// truncate shortens a string to maxLen, adding "..." if truncated
func truncate(s string, maxLen int) string {
	if len(s) <= maxLen {
		return s
	}
	if maxLen <= 3 {
		return s[:maxLen]
	}
	return s[:maxLen-3] + "..."
}

// Helper types for sorting
type countPair struct {
	key   string
	count int
}

// getTopN returns the top N items by count
func getTopN(m map[string]int, n int) []countPair {
	pairs := make([]countPair, 0, len(m))
	for k, v := range m {
		pairs = append(pairs, countPair{k, v})
	}

	// Simple bubble sort (fine for small datasets)
	for i := 0; i < len(pairs); i++ {
		for j := i + 1; j < len(pairs); j++ {
			if pairs[j].count > pairs[i].count {
				pairs[i], pairs[j] = pairs[j], pairs[i]
			}
		}
	}

	if len(pairs) > n {
		pairs = pairs[:n]
	}
	return pairs
}
