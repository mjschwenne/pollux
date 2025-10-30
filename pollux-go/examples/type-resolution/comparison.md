# Type Analysis Approaches in Go: A Comparison

This document compares different approaches to analyzing struct field types in Go, helping you choose the right tool for your use case.

## Overview of Approaches

| Approach | Complexity | Type Resolution | Use Case |
|----------|-----------|----------------|----------|
| **go/ast + go/parser** | Low | ❌ None | Basic syntax analysis |
| **go/types** | Medium | ✅ Full | Type-aware analysis |
| **go/packages** | Low | ✅ Full | Modern, high-level API |
| **Runtime reflection** | Medium | ⚠️ Partial | Runtime introspection |

## 1. go/ast + go/parser (Basic - Limited)

**What it does:** Parses Go source into an Abstract Syntax Tree

**Limitations:**
- Cannot resolve type aliases (`type MyInt int` stays as "MyInt")
- Cannot follow imports to other packages
- No type checking or validation
- Only sees what's literally written in the source

**Example:**

```go
package main

import (
    "go/ast"
    "go/parser"
    "go/token"
)

func analyzeWithAST(filename string) {
    fset := token.NewFileSet()
    file, _ := parser.ParseFile(fset, filename, nil, 0)
    
    ast.Inspect(file, func(n ast.Node) bool {
        if ts, ok := n.(*ast.TypeSpec); ok {
            if st, ok := ts.Type.(*ast.StructType); ok {
                for _, field := range st.Fields.List {
                    // ❌ Problem: field.Type only gives AST representation
                    // For "type MyInt int", you see "MyInt" not "int"
                    typeStr := types.ExprString(field.Type)
                    // typeStr = "MyInt" (not resolved!)
                }
            }
        }
        return true
    })
}
```

**When to use:**
- Simple syntax checking
- Code formatting tools
- When you only need surface-level information
- Performance-critical tools that don't need type info

## 2. go/types (Medium - Full Control)

**What it does:** Type-checks Go code and resolves all types

**Advantages:**
- ✅ Resolves type aliases to underlying types
- ✅ Handles imports and external dependencies
- ✅ Full type information without running code
- ✅ Fine-grained control over type checking

**Example:**

```go
package main

import (
    "go/importer"
    "go/parser"
    "go/token"
    "go/types"
)

func analyzeWithTypes(pkgPath string) {
    fset := token.NewFileSet()
    
    // Parse the package
    pkgs, _ := parser.ParseDir(fset, pkgPath, nil, 0)
    
    for _, pkg := range pkgs {
        var files []*ast.File
        for _, f := range pkg.Files {
            files = append(files, f)
        }
        
        // Configure type checker
        conf := types.Config{
            Importer: importer.ForCompiler(fset, "source", nil),
        }
        
        info := &types.Info{
            Types: make(map[ast.Expr]types.TypeAndValue),
        }
        
        // Type-check the package
        typedPkg, _ := conf.Check("example", fset, files, info)
        
        // Now you can iterate through types
        scope := typedPkg.Scope()
        for _, name := range scope.Names() {
            obj := scope.Lookup(name)
            if tn, ok := obj.(*types.TypeName); ok {
                if st, ok := tn.Type().Underlying().(*types.Struct); ok {
                    for i := 0; i < st.NumFields(); i++ {
                        field := st.Field(i)
                        
                        // ✅ Full type resolution!
                        declaredType := field.Type().String()        // "example.MyInt"
                        underlyingType := field.Type().Underlying().String() // "int"
                        
                        // ✅ Type categorization
                        switch field.Type().Underlying().(type) {
                        case *types.Basic:
                            // Basic type (int, string, etc.)
                        case *types.Struct:
                            // Struct type
                        case *types.Pointer:
                            // Pointer type
                        }
                    }
                }
            }
        }
    }
}
```

**When to use:**
- You need full type resolution
- You want fine-grained control
- You're building analysis tools
- You need to handle complex scenarios

**Limitations:**
- More verbose than go/packages
- Manual handling of imports and errors
- Requires understanding of type checker internals

## 3. go/packages (Modern - Recommended)

**What it does:** High-level API that wraps go/types with better ergonomics

**Advantages:**
- ✅ All benefits of go/types
- ✅ Handles Go modules automatically
- ✅ Much simpler API
- ✅ Better error handling
- ✅ Supports build tags and constraints

**Example:**

```go
package main

import (
    "go/types"
    "golang.org/x/tools/go/packages"
)

func analyzeWithPackages(pattern string) {
    // Load the package with type information
    cfg := &packages.Config{
        Mode: packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo,
    }
    
    pkgs, _ := packages.Load(cfg, pattern)
    
    for _, pkg := range pkgs {
        // Access the type-checked package
        scope := pkg.Types.Scope()
        
        for _, name := range scope.Names() {
            obj := scope.Lookup(name)
            if tn, ok := obj.(*types.TypeName); ok {
                if st, ok := tn.Type().Underlying().(*types.Struct); ok {
                    for i := 0; i < st.NumFields(); i++ {
                        field := st.Field(i)
                        
                        // ✅ Same type resolution as go/types
                        // but with much simpler setup!
                        declaredType := field.Type().String()
                        underlyingType := field.Type().Underlying().String()
                    }
                }
            }
        }
    }
}
```

**When to use:**
- Modern Go projects (Go 1.11+ with modules)
- You want the easiest API
- You need to work with multiple packages
- You want automatic handling of dependencies

**Installation:**
```bash
go get golang.org/x/tools/go/packages
```

## 4. Runtime Reflection (Dynamic)

**What it does:** Inspects types at runtime using `reflect` package

**Advantages:**
- Works with compiled code
- No parsing required
- Can inspect values, not just types

**Limitations:**
- ❌ Cannot analyze source files directly
- ❌ Requires loading/compiling the code
- ❌ Limited type alias information
- ❌ Runtime overhead
- ❌ May execute init() functions

**Example:**

```go
package main

import (
    "reflect"
    "fmt"
)

type MyInt int

type Example struct {
    Count MyInt
    Name  string
}

func analyzeWithReflection() {
    t := reflect.TypeOf(Example{})
    
    for i := 0; i < t.NumField(); i++ {
        field := t.Field(i)
        
        // ⚠️ Limited: Shows "main.MyInt" but harder to get "int"
        fmt.Println(field.Type.String())  // "main.MyInt"
        fmt.Println(field.Type.Kind())    // "int" (only for simple types)
        
        // ❌ Cannot handle complex type aliases well
        // ❌ Doesn't work on source files
    }
}
```

**When to use:**
- Runtime introspection of values
- Dynamic serialization/deserialization
- When you already have compiled code
- Plugin systems

**NOT suitable for:**
- Static analysis of source files
- Code generation from source
- Analyzing code before compilation

## Decision Matrix

### Choose **go/ast + go/parser** if:
- ✓ You only need syntax information
- ✓ Performance is critical
- ✓ You don't care about type resolution

### Choose **go/types** if:
- ✓ You need full type resolution
- ✓ You want fine-grained control
- ✓ You're building complex analysis tools
- ✓ You need to understand the type system deeply

### Choose **go/packages** if:
- ✓ You want the simplest API
- ✓ You're working with Go modules
- ✓ You need multi-package analysis
- ✓ You want good defaults and ergonomics
- ✓ **RECOMMENDED FOR MOST USE CASES**

### Choose **runtime reflection** if:
- ✓ You need to inspect runtime values
- ✓ You're working with compiled code
- ✓ You need dynamic behavior
- ✗ NOT for analyzing source files

## Real-World Example: Type Alias Resolution

Given this code:

```go
package example

type UserID int
type ProductID int

type Order struct {
    User    UserID
    Product ProductID
    Total   float64
}
```

### With go/ast (❌ Cannot differentiate):
```
User    -> "UserID"
Product -> "ProductID"
Total   -> "float64"
```
You cannot tell that UserID and ProductID are both `int`.

### With go/types or go/packages (✅ Full resolution):
```
User    -> Declared: "UserID"    Underlying: "int"
Product -> Declared: "ProductID" Underlying: "int"
Total   -> Declared: "float64"   Underlying: "float64"
```
You can see both the semantic type AND the underlying type!

### With reflection (⚠️ Runtime only):
```
User    -> Kind: "int", Type: "example.UserID"
Product -> Kind: "int", Type: "example.ProductID"
Total   -> Kind: "float64", Type: "float64"
```
Works, but requires compiled code and runtime execution.

## Recommendation for Your Use Case

Based on your question about analyzing struct field types:

**Use `go/types`** if you want to learn the fundamentals and have full control.

**Use `go/packages`** if you want to get things done quickly with modern Go.

**Avoid runtime reflection** for this use case - it's not designed for source code analysis.

## Complete Example with go/packages

```go
package main

import (
    "fmt"
    "go/types"
    "log"
    "golang.org/x/tools/go/packages"
)

func main() {
    cfg := &packages.Config{
        Mode: packages.NeedTypes | packages.NeedTypesInfo,
    }
    
    pkgs, err := packages.Load(cfg, "./your/package/path")
    if err != nil {
        log.Fatal(err)
    }
    
    for _, pkg := range pkgs {
        scope := pkg.Types.Scope()
        
        for _, name := range scope.Names() {
            obj := scope.Lookup(name)
            tn, ok := obj.(*types.TypeName)
            if !ok {
                continue
            }
            
            structType, ok := tn.Type().Underlying().(*types.Struct)
            if !ok {
                continue
            }
            
            fmt.Printf("Struct: %s\n", name)
            
            for i := 0; i < structType.NumFields(); i++ {
                field := structType.Field(i)
                fmt.Printf("  %s: %s (underlying: %s)\n",
                    field.Name(),
                    field.Type(),
                    field.Type().Underlying())
            }
        }
    }
}
```

This gives you everything you need: type resolution, alias handling, and distribution analysis!