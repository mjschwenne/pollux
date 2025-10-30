# Solution: Analyzing Struct Field Types in Go

## Your Question

You asked about analyzing the distribution of types defined in struct fields in Go files, specifically:
- Whether reflection works (it doesn't for source files)
- Whether AST/parser can differentiate named types from basic types (it can't)
- How to resolve types to enable comparison

## The Answer: Use `go/types` Package

**Yes, it is absolutely possible to resolve types!** The `go/types` package is specifically designed for this purpose.

## Why Reflection Doesn't Work for Your Use Case

Runtime reflection (`reflect` package) has these limitations:

❌ **Cannot analyze source files directly** - Only works with compiled code
❌ **Requires loading/executing code** - May run `init()` functions
❌ **Limited type alias resolution** - Hard to get underlying types consistently
❌ **Not designed for static analysis** - Built for runtime introspection

**Verdict:** Don't use reflection for analyzing source code.

## Why AST/Parser Alone Isn't Enough

The `go/ast` and `go/parser` packages give you syntax trees but:

❌ **No type resolution** - `type MyInt int` stays as "MyInt"
❌ **Cannot follow imports** - External types are just identifiers
❌ **No type checking** - Can't distinguish valid from invalid types

**Example problem:**
```go
type UserID int
type ProductID int

type Order struct {
    User    UserID    // AST sees "UserID"
    Product ProductID // AST sees "ProductID"
}
```

With AST alone, you cannot tell that both `UserID` and `ProductID` are actually `int`.

## The Solution: go/types

The `go/types` package performs **type checking** and resolves all types, including:

✅ Type aliases to their underlying types
✅ Imports from external packages
✅ Named types vs basic types
✅ Complex type structures

### Basic Example

```go
package main

import (
    "go/importer"
    "go/parser"
    "go/token"
    "go/types"
)

func analyzeStructTypes(pkgPath string) {
    // 1. Parse the source code
    fset := token.NewFileSet()
    pkgs, _ := parser.ParseDir(fset, pkgPath, nil, 0)
    
    for pkgName, pkg := range pkgs {
        // 2. Collect files for type checking
        var files []*ast.File
        for _, f := range pkg.Files {
            files = append(files, f)
        }
        
        // 3. Configure the type checker
        conf := types.Config{
            Importer: importer.ForCompiler(fset, "source", nil),
        }
        
        info := &types.Info{
            Types: make(map[ast.Expr]types.TypeAndValue),
        }
        
        // 4. Type-check the package
        typedPkg, _ := conf.Check(pkgName, fset, files, info)
        
        // 5. Iterate through all types in the package
        scope := typedPkg.Scope()
        for _, name := range scope.Names() {
            obj := scope.Lookup(name)
            typeName, ok := obj.(*types.TypeName)
            if !ok {
                continue
            }
            
            // 6. Check if it's a struct
            structType, ok := typeName.Type().Underlying().(*types.Struct)
            if !ok {
                continue
            }
            
            // 7. Analyze each field
            for i := 0; i < structType.NumFields(); i++ {
                field := structType.Field(i)
                fieldType := field.Type()
                
                // KEY INSIGHT: Get both declared and underlying types
                declared := fieldType.String()        // e.g., "main.UserID"
                underlying := fieldType.Underlying().String() // e.g., "int"
                
                // Now you can compare types correctly!
                if underlying == "int" {
                    // This field is ultimately an int
                }
            }
        }
    }
}
```

### Key Methods

```go
// Get the type as declared in source
fieldType.String()  // "main.UserID" or "string"

// Get the underlying type (resolves aliases)
fieldType.Underlying().String()  // "int" or "string"

// Check the category
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
}
```

## Even Simpler: Use go/packages

For modern Go projects, `go/packages` provides a higher-level API:

```go
package main

import (
    "go/types"
    "golang.org/x/tools/go/packages"
)

func analyzeWithPackages(pattern string) {
    cfg := &packages.Config{
        Mode: packages.NeedTypes | packages.NeedTypesInfo,
    }
    
    pkgs, _ := packages.Load(cfg, pattern)
    
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
            
            // Analyze fields
            for i := 0; i < st.NumFields(); i++ {
                field := st.Field(i)
                
                declared := field.Type().String()
                underlying := field.Type().Underlying().String()
                
                // Compare types!
            }
        }
    }
}
```

**Advantages of go/packages:**
- Automatically handles Go modules
- Simpler API than go/types
- Better error handling
- Supports build tags

**Installation:**
```bash
go get golang.org/x/tools/go/packages
```

## Practical Example: Type Distribution

Here's how to build a type distribution analyzer:

```go
func analyzeTypeDistribution(pkgPath string) map[string]int {
    distribution := make(map[string]int)
    
    cfg := &packages.Config{
        Mode: packages.NeedTypes | packages.NeedTypesInfo,
    }
    
    pkgs, _ := packages.Load(cfg, pkgPath)
    
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
            
            for i := 0; i < st.NumFields(); i++ {
                field := st.Field(i)
                
                // Count by underlying type
                underlyingType := field.Type().Underlying().String()
                distribution[underlyingType]++
            }
        }
    }
    
    return distribution
}
```

**Output example:**
```
string: 15
int: 10
bool: 5
float64: 3
*User: 2
[]string: 2
map[string]int: 1
```

## Real-World Use Cases

This technique enables:

1. **Type Distribution Analysis** - Understand what types are used most
2. **Code Generation** - Generate serializers, validators, ORMs
3. **Schema Validation** - Compare Go structs to database schemas
4. **Refactoring Tools** - Find all uses of specific types
5. **Documentation** - Auto-generate type documentation
6. **Linting** - Enforce type usage policies

## Complete Working Example

I've created a full implementation in this repository:

- **`cmd/struct-analyzer/main.go`** - Complete analyzer tool
- **`examples/type-resolution/simple_example.go`** - Basic demonstration
- **`examples/type-resolution/packages_example.go`** - Using go/packages
- **`examples/type-resolution/comparison.md`** - Detailed comparison

**Run the analyzer:**
```bash
cd cmd/struct-analyzer
go run main.go -pkg ../../testdata/json -v
```

**Output:**
```
=== Struct Field Type Distribution ===

Total fields analyzed: 54

--- By Category ---
  Basic          :   35 (64.8%)
  Struct         :    7 (13.0%)
  Map            :    2 (3.7%)
  Interface      :    2 (3.7%)
  Pointer        :    2 (3.7%)
  ...

--- By Underlying Type ---
  string                        :   10 (18.5%)
  int                           :    8 (14.8%)
  uint                          :    2 (3.7%)
  ...
```

## Recommendation

**For your use case (analyzing struct field types in source files):**

1. **Start with `go/packages`** - Simplest, most modern approach
2. **Fall back to `go/types`** - If you need fine-grained control
3. **Avoid runtime reflection** - Not designed for source analysis

## Summary

✅ **YES, you can resolve types** using `go/types`
✅ **YES, you can differentiate** named types from their underlying types
✅ **YES, you can compare types** accurately across files
✅ **NO, you don't need reflection** for source code analysis

The key insight is that `Type().Underlying()` resolves all type aliases, allowing you to:
- Compare types accurately
- Build distribution statistics
- Generate code based on actual types
- Perform static analysis without execution

See the complete examples in this directory for working code!