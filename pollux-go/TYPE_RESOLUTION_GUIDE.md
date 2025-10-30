# Guide: Analyzing Struct Field Types in Go

## Executive Summary

**Question:** How do I analyze the distribution of types in Go struct fields when type aliases like `type MyInt int` make it hard to differentiate types?

**Answer:** Use the `go/types` package (or the higher-level `go/packages` API) to perform type checking and resolution. This resolves all type aliases to their underlying types, enabling accurate type comparison and distribution analysis.

## The Problem

You have Go source files with structs that use type aliases:

```go
type MyInt int
type MyString string

type Example struct {
    Count   MyInt      // Type alias
    Label   MyString   // Type alias
    Name    string     // Basic type
}
```

**Challenge:** How do you determine that `Count` and `Name` are both ultimately integers, while `Label` and `Name` are both strings?

- ❌ **Runtime reflection** doesn't work - requires compiled code, not source files
- ❌ **AST parsing alone** doesn't resolve aliases - you just see "MyInt" not "int"
- ✅ **go/types package** solves this - performs type checking and resolves all aliases

## The Solution: go/types

The `go/types` package is Go's type-checker. It:

1. Parses Go source code (using `go/parser`)
2. Performs type checking
3. Resolves all type aliases to their underlying types
4. Provides complete type information for analysis

### Quick Example

```go
package main

import (
    "fmt"
    "go/types"
    "golang.org/x/tools/go/packages"
)

func main() {
    // Load package with type information
    cfg := &packages.Config{
        Mode: packages.NeedTypes | packages.NeedTypesInfo,
    }
    pkgs, _ := packages.Load(cfg, "./your/package")
    
    // Analyze all structs
    for _, pkg := range pkgs {
        scope := pkg.Types.Scope()
        for _, name := range scope.Names() {
            obj := scope.Lookup(name)
            tn, ok := obj.(*types.TypeName)
            if !ok {
                continue
            }
            
            st, ok := tn.Type().Underlying().(*types.Struct)
            if !ok {
                continue
            }
            
            // Analyze each field
            fmt.Printf("Struct: %s\n", name)
            for i := 0; i < st.NumFields(); i++ {
                field := st.Field(i)
                
                // KEY: Get both declared and underlying types
                declared := field.Type().String()           // "main.MyInt"
                underlying := field.Type().Underlying().String() // "int"
                
                fmt.Printf("  %s: %s -> %s\n", field.Name(), declared, underlying)
            }
        }
    }
}
```

**Install the packages library:**
```bash
go get golang.org/x/tools/go/packages
```

## Key Concepts

### 1. Type Resolution

```go
// Given: type MyInt int
fieldType.String()             // "main.MyInt" (declared type)
fieldType.Underlying().String() // "int" (underlying type)
```

The `.Underlying()` method is the key - it resolves all type aliases.

### 2. Type Categorization

```go
// Categorize by underlying structure
switch fieldType.Underlying().(type) {
case *types.Basic:
    // int, string, bool, float64, etc.
case *types.Struct:
    // struct types
case *types.Pointer:
    // *T
case *types.Slice:
    // []T
case *types.Array:
    // [N]T
case *types.Map:
    // map[K]V
case *types.Chan:
    // chan T
case *types.Signature:
    // func types
case *types.Interface:
    // interface types
}
```

### 3. Type Distribution Analysis

```go
// Count types by their underlying type
distribution := make(map[string]int)

for i := 0; i < structType.NumFields(); i++ {
    field := structType.Field(i)
    underlyingType := field.Type().Underlying().String()
    distribution[underlyingType]++
}

// Result: map[string]int{
//   "int": 10,
//   "string": 15,
//   "bool": 5,
//   ...
// }
```

## Comparison: Different Approaches

| Approach | Type Resolution | Works on Source | Use Case |
|----------|----------------|-----------------|----------|
| **go/ast + go/parser** | ❌ None | ✅ Yes | Syntax analysis only |
| **go/types** | ✅ Full | ✅ Yes | Type-aware analysis (manual) |
| **go/packages** | ✅ Full | ✅ Yes | Type-aware analysis (easy) |
| **runtime reflection** | ⚠️ Limited | ❌ No | Runtime introspection |

### Recommendation

- **Use `go/packages`** - Simplest API, handles Go modules automatically
- **Use `go/types`** - If you need fine-grained control over type checking
- **Avoid reflection** - Not designed for source code analysis

## Complete Working Examples

This repository includes several working examples:

### 1. Full Analyzer Tool
Location: `cmd/struct-analyzer/main.go`

A complete tool that analyzes struct field types and generates distribution statistics.

```bash
cd cmd/struct-analyzer
go run main.go -pkg ../../testdata/json -v
```

Output:
```
=== Struct Field Type Distribution ===

Total fields analyzed: 54

--- By Category ---
  Basic          :   35 (64.8%)
  Struct         :    7 (13.0%)
  Map            :    2 (3.7%)
  ...

--- By Underlying Type ---
  string         :   10 (18.5%)
  int            :    8 (14.8%)
  ...
```

### 2. Simple Examples
Location: `examples/type-resolution/`

- `simple_example.go` - Basic demonstration of type resolution
- `packages_example.go` - Using go/packages API
- `sample.go` - Test data with various type aliases

```bash
cd examples/type-resolution
go run simple_example.go
```

### 3. Documentation
- `examples/type-resolution/SOLUTION.md` - Comprehensive explanation
- `examples/type-resolution/QUICKSTART.md` - 5-minute quick start
- `examples/type-resolution/comparison.md` - Detailed approach comparison

## Real-World Use Cases

This technique enables:

1. **Type Distribution Analysis** - Understand what types are used in your codebase
2. **Code Generation** - Generate serializers, validators, ORM mappings
3. **Schema Validation** - Compare Go structs to database/API schemas
4. **Refactoring Tools** - Find all uses of specific types
5. **Documentation Generation** - Auto-generate type documentation
6. **Linting/Code Quality** - Enforce type usage policies
7. **Migration Tools** - Track type changes across versions

## Why This Matters

### Example Scenario

You have multiple microservices with similar struct definitions:

```go
// Service A
type UserID string
type User struct { ID UserID }

// Service B  
type UserID int64
type User struct { ID UserID }
```

**Problem:** Both use `UserID` but with different underlying types!

**Solution:** Use go/types to detect this inconsistency:

```go
// In Service A: UserID -> string
// In Service B: UserID -> int64
// MISMATCH DETECTED!
```

This prevents runtime errors and API incompatibilities.

## Key Takeaways

✅ **YES** - You can resolve type aliases to their underlying types
✅ **YES** - You can differentiate named types from basic types
✅ **YES** - You can compare types accurately across files
✅ **NO** - You don't need runtime reflection for source analysis

**The Magic Method:** `Type().Underlying()` resolves all aliases

**Recommended API:** `golang.org/x/tools/go/packages` for simplicity

**Core Insight:** Go's type checker does the heavy lifting - you just need to invoke it!

## Getting Started

1. **Quick Start:** Read `examples/type-resolution/QUICKSTART.md`
2. **Deep Dive:** Read `examples/type-resolution/SOLUTION.md`
3. **Run Examples:** Execute the examples in `examples/type-resolution/`
4. **Use the Tool:** Try `cmd/struct-analyzer` on your own code
5. **Build Your Own:** Use the patterns from the examples

## Further Reading

- [go/types documentation](https://pkg.go.dev/go/types)
- [go/packages documentation](https://pkg.go.dev/golang.org/x/tools/go/packages)
- [Go AST documentation](https://pkg.go.dev/go/ast)
- [Tutorial: Writing Go Tools](https://pkg.go.dev/golang.org/x/tools/go/analysis)

## Summary

The answer to your question is: **Use the `go/types` package** (or `go/packages` for a simpler API). It performs type checking on source code and resolves all type aliases, enabling you to:

- Determine underlying types (e.g., `MyInt` → `int`)
- Compare types accurately
- Build type distribution statistics
- Differentiate between semantically different types with the same underlying type

No runtime reflection needed - this is all done statically on source code!