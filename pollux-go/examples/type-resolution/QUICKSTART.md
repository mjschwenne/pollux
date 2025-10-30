# Quick Start: Type Resolution in Go

## TL;DR

**Problem:** You need to analyze struct field types in Go source files, but `go/ast` alone can't resolve type aliases like `type MyInt int`.

**Solution:** Use `go/types` or `go/packages` to get full type resolution.

## 5-Minute Solution

### Option 1: Using go/packages (Recommended)

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
    
    // Analyze structs
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
            
            // Got a struct! Analyze fields
            fmt.Printf("Struct: %s\n", name)
            for i := 0; i < st.NumFields(); i++ {
                field := st.Field(i)
                
                // KEY: Get both declared and underlying types
                fmt.Printf("  %s: %s (underlying: %s)\n",
                    field.Name(),
                    field.Type(),           // "MyInt"
                    field.Type().Underlying()) // "int"
            }
        }
    }
}
```

**Install:**
```bash
go get golang.org/x/tools/go/packages
```

### Option 2: Using go/types (More Control)

```go
package main

import (
    "go/importer"
    "go/parser"
    "go/token"
    "go/types"
)

func main() {
    fset := token.NewFileSet()
    pkgs, _ := parser.ParseDir(fset, "./your/package", nil, 0)
    
    for pkgName, pkg := range pkgs {
        var files []*ast.File
        for _, f := range pkg.Files {
            files = append(files, f)
        }
        
        conf := types.Config{
            Importer: importer.ForCompiler(fset, "source", nil),
        }
        info := &types.Info{
            Types: make(map[ast.Expr]types.TypeAndValue),
        }
        
        typedPkg, _ := conf.Check(pkgName, fset, files, info)
        
        // Same analysis code as above...
    }
}
```

## Key Concepts

### 1. Type Resolution

```go
// Given: type MyInt int

fieldType.String()             // "main.MyInt"
fieldType.Underlying().String() // "int"
```

### 2. Type Categorization

```go
switch fieldType.Underlying().(type) {
case *types.Basic:      // int, string, bool, etc.
case *types.Struct:     // struct types
case *types.Pointer:    // *T
case *types.Slice:      // []T
case *types.Array:      // [N]T
case *types.Map:        // map[K]V
case *types.Chan:       // chan T
case *types.Signature:  // func types
case *types.Interface:  // interface{}
}
```

### 3. Type Comparison

```go
// Compare underlying types
if field1.Type().Underlying().String() == field2.Type().Underlying().String() {
    // Same underlying type!
}

// Check if it's an int (including type aliases)
if basic, ok := field.Type().Underlying().(*types.Basic); ok {
    if basic.Kind() == types.Int {
        // This is an int!
    }
}
```

## Examples in This Repository

Run the examples:

```bash
# Simple demonstration
cd examples/type-resolution
go run simple_example.go

# Using go/packages
go run packages_example.go sample.go

# Full analyzer tool
cd ../../cmd/struct-analyzer
go run main.go -pkg ../../testdata/json -v
```

## Common Use Cases

### Get Type Distribution

```go
distribution := make(map[string]int)

for i := 0; i < structType.NumFields(); i++ {
    field := structType.Field(i)
    underlyingType := field.Type().Underlying().String()
    distribution[underlyingType]++
}

// Result: {"int": 10, "string": 5, "bool": 2, ...}
```

### Find All Int Fields (Including Aliases)

```go
for i := 0; i < structType.NumFields(); i++ {
    field := structType.Field(i)
    if basic, ok := field.Type().Underlying().(*types.Basic); ok {
        if basic.Kind() == types.Int {
            fmt.Printf("%s is an int\n", field.Name())
        }
    }
}
```

### Categorize Fields

```go
categories := map[string][]string{
    "basic": {},
    "composite": {},
    "reference": {},
}

for i := 0; i < structType.NumFields(); i++ {
    field := structType.Field(i)
    underlying := field.Type().Underlying()
    
    switch underlying.(type) {
    case *types.Basic:
        categories["basic"] = append(categories["basic"], field.Name())
    case *types.Slice, *types.Array, *types.Map, *types.Struct:
        categories["composite"] = append(categories["composite"], field.Name())
    case *types.Pointer, *types.Chan:
        categories["reference"] = append(categories["reference"], field.Name())
    }
}
```

## FAQ

**Q: Can I use reflection instead?**
A: No, reflection requires compiled code. Use go/types for source analysis.

**Q: Does this work with type aliases?**
A: Yes! That's the whole point. `Type().Underlying()` resolves aliases.

**Q: What about generic types (Go 1.18+)?**
A: go/types supports generics. Use `types.TypeParam` for type parameters.

**Q: Can I analyze code from other modules?**
A: Yes! go/packages handles imports automatically.

**Q: Is this slow for large codebases?**
A: Type checking has overhead. Cache results if analyzing repeatedly.

**Q: go/types vs go/packages?**
A: Use go/packages for simplicity, go/types for fine control.

## Next Steps

1. **Read:** `SOLUTION.md` for complete explanation
2. **Compare:** `comparison.md` for approach comparison
3. **Run:** Examples in this directory
4. **Build:** Your own analyzer using the patterns here

## One-Liner Takeaway

Use `Type().Underlying()` to resolve type aliases, then categorize with type switches.

That's it! 🎉