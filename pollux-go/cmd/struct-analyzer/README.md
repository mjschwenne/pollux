# Struct Field Type Analyzer

This tool demonstrates how to analyze Go struct field types using the `go/types` package, which resolves type aliases and provides complete type information without needing runtime reflection.

## The Problem

When analyzing Go source code, you often need to understand the actual types used in struct fields. This is challenging because:

1. **Runtime reflection** requires loading and executing code, which is complex for static analysis
2. **AST parsing alone** (`go/ast` + `go/parser`) doesn't resolve type aliases like `type MyInt int`
3. You need to distinguish between basic types, named types, and struct types from other packages

## The Solution: go/types

The `go/types` package provides a type-checker that:

- ✅ Resolves type aliases to their underlying types (e.g., `MyInt` → `int`)
- ✅ Handles imports and external dependencies
- ✅ Provides complete type information without executing code
- ✅ Works on source code statically
- ✅ Distinguishes between named types, basic types, and complex types

## Architecture

```
Source Files → go/parser → AST → go/types (type checker) → Type Information
                   ↓                        ↓
              go/token.FileSet      types.Info (resolved types)
```

### Key Components

1. **`go/parser`**: Parses Go source files into an Abstract Syntax Tree (AST)
2. **`go/types`**: Type-checks the AST and resolves all types
3. **`types.Info`**: Stores mapping from AST nodes to their resolved types
4. **`types.Config`**: Configures the type checker (handles imports, errors, etc.)

## Usage

```bash
# Analyze a package (default: ./testdata/json)
go run main.go

# Analyze a specific package
go run main.go -pkg /path/to/package

# Show verbose output with all fields
go run main.go -v

# Show breakdown of basic types
go run main.go -basic

# Combine flags
go run main.go -pkg ../../testdata/json -v -basic
```

## Example Output

```
=== Struct Field Type Distribution ===

Total fields analyzed: 54

--- By Category ---
  Basic          :   35 (64.8%)
  Struct         :    7 (13.0%)
  Map            :    2 (3.7%)
  Interface      :    2 (3.7%)
  Pointer        :    2 (3.7%)
  Slice          :    2 (3.7%)
  UnsafePointer  :    1 (1.9%)
  Array          :    1 (1.9%)
  Chan           :    1 (1.9%)
  Func           :    1 (1.9%)

--- By Underlying Type ---
  string                        :   10 (18.5%)
  int                           :    8 (14.8%)
  uint                          :    2 (3.7%)
  ...
```

With `-v` flag, you'll see individual field analysis:
```
  AllKinds.MyIntField: main.MyInt -> int (Basic)
  AllKinds.StructField: struct{X int} -> struct{X int} (Struct)
  AllKinds.PointerField: *int -> *int (Pointer)
```

Notice how `MyIntField` shows both the declared type (`main.MyInt`) and the underlying type (`int`).

## How It Works

### Step 1: Parse the Package

```go
fset := token.NewFileSet()
pkgs, err := parser.ParseDir(fset, pkgPath, func(fi os.FileInfo) bool {
    return !strings.HasSuffix(fi.Name(), "_test.go")
}, 0)
```

This parses all Go files (excluding tests) into AST representations.

### Step 2: Configure the Type Checker

```go
conf := types.Config{
    Importer: importer.ForCompiler(fset, "source", nil),
    Error: func(err error) {
        // Handle type checking errors
    },
}

info := &types.Info{
    Types: make(map[ast.Expr]types.TypeAndValue),
    Defs:  make(map[*ast.Ident]types.Object),
    Uses:  make(map[*ast.Ident]types.Object),
}
```

The `Importer` resolves external package dependencies. The `Info` struct stores the resolved type information.

### Step 3: Type-Check the Package

```go
typedPkg, err := conf.Check(pkgName, fset, files, info)
```

This performs type checking and populates `info` with resolved type information.

### Step 4: Iterate Through Structs

```go
scope := typedPkg.Scope()
for _, name := range scope.Names() {
    obj := scope.Lookup(name)
    typeName, ok := obj.(*types.TypeName)
    if !ok {
        continue
    }
    
    // Check if it's a struct
    if structType, ok := typeName.Type().Underlying().(*types.Struct); ok {
        // Analyze struct fields
    }
}
```

### Step 5: Analyze Field Types

```go
for i := 0; i < structType.NumFields(); i++ {
    field := structType.Field(i)
    fieldType := field.Type()
    
    // Get the underlying type (resolves aliases)
    underlyingType := fieldType.Underlying()
    
    // Categorize the type
    switch underlying := underlyingType.(type) {
    case *types.Basic:
        // int, string, bool, etc.
    case *types.Struct:
        // struct types
    case *types.Pointer:
        // pointer types
    // ... etc
    }
}
```

## Key Insights

### Type Resolution

The key insight is using `Type().Underlying()` to resolve aliases:

```go
// Given: type MyInt int
fieldType.String()             // "main.MyInt"
fieldType.Underlying().String() // "int"
```

### Type Categorization

You can categorize types by their underlying structure:

```go
switch fieldType.Underlying().(type) {
case *types.Basic:      // int, string, bool, float64, etc.
case *types.Struct:     // struct types
case *types.Pointer:    // *T
case *types.Slice:      // []T
case *types.Array:      // [N]T
case *types.Map:        // map[K]V
case *types.Chan:       // chan T
case *types.Signature:  // func types
case *types.Interface:  // interface types
}
```

### Named vs. Underlying Types

For named types (type aliases), you can distinguish:

```go
if named, ok := fieldType.(*types.Named); ok {
    // This is a named type (e.g., MyInt)
    namedStr := named.String()           // "main.MyInt"
    underlyingStr := named.Underlying().String() // "int"
}
```

## Advantages Over Runtime Reflection

| Feature | go/types | Runtime Reflection |
|---------|----------|-------------------|
| **Static Analysis** | ✅ Works on source | ❌ Needs compiled code |
| **Type Resolution** | ✅ Full resolution | ⚠️ Limited |
| **Performance** | ✅ Fast parsing | ⚠️ Runtime overhead |
| **External Packages** | ✅ Handles imports | ❌ Must be loaded |
| **Partial Code** | ✅ Can analyze incomplete code | ❌ Needs complete build |
| **No Execution** | ✅ Purely static | ❌ May execute init() |

## Common Use Cases

1. **Code Analysis**: Understand struct composition and field types
2. **Code Generation**: Generate serialization, validation, or ORM code
3. **Linting**: Enforce coding standards on struct fields
4. **Documentation**: Generate type documentation automatically
5. **Refactoring**: Find all uses of specific types
6. **Schema Validation**: Ensure structs match database schemas

## Further Reading

- [go/types documentation](https://pkg.go.dev/go/types)
- [go/ast documentation](https://pkg.go.dev/go/ast)
- [golang.org/x/tools/go/packages](https://pkg.go.dev/golang.org/x/tools/go/packages) - Higher-level API
- [Tutorial: Writing Go Tools](https://pkg.go.dev/golang.org/x/tools/go/analysis)

## Tips

1. **Use `go/packages`** for more complex analysis - it's a higher-level API that handles module resolution better
2. **Handle errors gracefully** - partial type information is often useful even with errors
3. **Cache results** - type checking can be expensive for large codebases
4. **Test with edge cases** - unnamed structs, embedded fields, generic types (Go 1.18+)