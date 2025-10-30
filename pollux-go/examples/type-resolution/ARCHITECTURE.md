# Architecture: Type Resolution in Go

## Overview Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Go Source Files                              │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │ type MyInt int                                                  │ │
│  │ type UserID string                                              │ │
│  │                                                                 │ │
│  │ type User struct {                                              │ │
│  │     ID    UserID  // Named type                                │ │
│  │     Age   MyInt   // Type alias                                │ │
│  │     Name  string  // Basic type                                │ │
│  │     Tags  []string                                              │ │
│  │ }                                                               │ │
│  └────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      go/parser + go/token                            │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │  fset := token.NewFileSet()                                     │ │
│  │  file, _ := parser.ParseFile(fset, "source.go", src, 0)        │ │
│  └────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    Abstract Syntax Tree (AST)                        │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │  *ast.File                                                      │ │
│  │    └─ *ast.TypeSpec (User)                                      │ │
│  │         └─ *ast.StructType                                      │ │
│  │              ├─ *ast.Field (ID, type: *ast.Ident "UserID")     │ │
│  │              ├─ *ast.Field (Age, type: *ast.Ident "MyInt")     │ │
│  │              ├─ *ast.Field (Name, type: *ast.Ident "string")   │ │
│  │              └─ *ast.Field (Tags, type: *ast.ArrayType)        │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ⚠️  Problem: AST only shows identifiers, not resolved types!       │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     go/types (Type Checker)                          │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │  conf := types.Config{                                          │ │
│  │      Importer: importer.Default(),                              │ │
│  │  }                                                              │ │
│  │  info := &types.Info{                                           │ │
│  │      Types: make(map[ast.Expr]types.TypeAndValue),             │ │
│  │  }                                                              │ │
│  │  pkg, _ := conf.Check("main", fset, files, info)               │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ✅ Performs type checking and resolution                           │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     Resolved Type Information                        │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │  *types.Package                                                 │ │
│  │    └─ Scope                                                     │ │
│  │         ├─ "UserID" → *types.TypeName                           │ │
│  │         │               Type: *types.Named (underlying: string) │ │
│  │         ├─ "MyInt" → *types.TypeName                            │ │
│  │         │              Type: *types.Named (underlying: int)     │ │
│  │         └─ "User" → *types.TypeName                             │ │
│  │                       Type: *types.Named                        │ │
│  │                       Underlying: *types.Struct                 │ │
│  │                         Fields:                                 │ │
│  │                           ├─ ID: UserID → string ✓              │ │
│  │                           ├─ Age: MyInt → int ✓                 │ │
│  │                           ├─ Name: string → string              │ │
│  │                           └─ Tags: []string → []string          │ │
│  └────────────────────────────────────────────────────────────────┘ │
│                                                                      │
│  ✅ Types are fully resolved!                                        │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        Your Analysis Code                            │
│  ┌────────────────────────────────────────────────────────────────┐ │
│  │  for i := 0; i < structType.NumFields(); i++ {                 │ │
│  │      field := structType.Field(i)                               │ │
│  │                                                                 │ │
│  │      declared := field.Type().String()                          │ │
│  │      // "main.UserID", "main.MyInt", "string", "[]string"      │ │
│  │                                                                 │ │
│  │      underlying := field.Type().Underlying().String()           │ │
│  │      // "string", "int", "string", "[]string"                  │ │
│  │  }                                                              │ │
│  └────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

## Component Breakdown

### 1. go/parser (Syntax Analysis)

**Purpose:** Parse Go source into AST

```
Input:  Go source code (string or file)
Output: *ast.File (abstract syntax tree)
```

**Limitations:**
- Only understands syntax, not semantics
- Type names are just identifiers
- Cannot resolve imports
- No type checking

**Example:**
```go
fset := token.NewFileSet()
file, err := parser.ParseFile(fset, "example.go", src, 0)
// file.Decls contains declarations but types are unresolved
```

### 2. go/types (Type Checking)

**Purpose:** Type-check AST and resolve all types

```
Input:  AST + configuration
Output: *types.Package + *types.Info
```

**Capabilities:**
- ✅ Resolves type aliases
- ✅ Follows imports
- ✅ Validates type correctness
- ✅ Provides complete type information

**Example:**
```go
conf := types.Config{
    Importer: importer.Default(),
}
info := &types.Info{
    Types: make(map[ast.Expr]types.TypeAndValue),
}
pkg, err := conf.Check("example", fset, []*ast.File{file}, info)
```

### 3. types.Info (Resolution Map)

**Purpose:** Maps AST nodes to their resolved types

```
Types map[ast.Expr]types.TypeAndValue  // Expression → Type
Defs  map[*ast.Ident]types.Object      // Definition → Object
Uses  map[*ast.Ident]types.Object      // Usage → Object
```

**Example:**
```go
// For expression "x + y"
tv := info.Types[expr]
tv.Type  // The type of the expression
tv.Value // The constant value (if constant)
```

## Type Hierarchy

```
types.Type (interface)
    │
    ├─ *types.Basic ─────────── int, string, bool, float64, etc.
    │
    ├─ *types.Named ─────────── type MyInt int
    │     │                      (has Underlying() method)
    │     └─ Underlying() ────→ points to actual type
    │
    ├─ *types.Struct ────────── struct { X int; Y string }
    │
    ├─ *types.Pointer ───────── *T
    │
    ├─ *types.Slice ─────────── []T
    │
    ├─ *types.Array ─────────── [N]T
    │
    ├─ *types.Map ───────────── map[K]V
    │
    ├─ *types.Chan ──────────── chan T
    │
    ├─ *types.Signature ─────── func(int) string
    │
    └─ *types.Interface ─────── interface { Method() }
```

## Key Methods

### Type Resolution

```go
// Given: type MyInt int

field.Type()              // Returns: *types.Named "MyInt"
field.Type().String()     // Returns: "main.MyInt"
field.Type().Underlying() // Returns: *types.Basic (int)
field.Type().Underlying().String() // Returns: "int"
```

### Type Inspection

```go
// Check if type is a named type
if named, ok := t.(*types.Named); ok {
    fmt.Println("Named:", named.Obj().Name())
    fmt.Println("Underlying:", named.Underlying())
}

// Check the underlying structure
switch u := t.Underlying().(type) {
case *types.Basic:
    fmt.Println("Basic type:", u.Name())
case *types.Struct:
    fmt.Println("Struct with", u.NumFields(), "fields")
case *types.Pointer:
    fmt.Println("Pointer to:", u.Elem())
}
```

## Workflow Comparison

### ❌ AST Only (Incomplete)

```
Source Code
    ↓ parse
AST (identifiers only)
    ↓ analyze
Limited Info: "UserID" is just a string
```

**Result:** Cannot distinguish `type UserID int` from `type UserID string`

### ✅ AST + go/types (Complete)

```
Source Code
    ↓ parse
AST (identifiers only)
    ↓ type-check
Resolved Types
    ↓ analyze
Complete Info: "UserID" resolves to "int"
```

**Result:** Full type resolution with underlying types

## Data Flow: Real Example

### Input Code
```go
type UserID int
type User struct {
    ID   UserID
    Name string
}
```

### Processing Pipeline

1. **Parser Output (AST)**
   ```
   TypeSpec(User) {
     StructType {
       Field(ID, Ident("UserID"))    ← Just an identifier!
       Field(Name, Ident("string"))
     }
   }
   ```

2. **Type Checker Output**
   ```
   Package Scope:
     "UserID" → TypeName{
       Type: Named{
         Name: "UserID"
         Underlying: Basic(Int)  ← Resolved!
       }
     }
     "User" → TypeName{
       Type: Named{
         Name: "User"
         Underlying: Struct{
           Field(ID, Named("UserID") → Basic(Int))
           Field(Name, Basic(String))
         }
       }
     }
   ```

3. **Your Analysis**
   ```
   Field: ID
     Declared:   "main.UserID"
     Underlying: "int"          ← Can compare!
   
   Field: Name
     Declared:   "string"
     Underlying: "string"
   ```

## Performance Characteristics

```
┌────────────────────┬─────────┬──────────┬─────────────┐
│ Operation          │ Speed   │ Memory   │ Accuracy    │
├────────────────────┼─────────┼──────────┼─────────────┤
│ Parse (AST only)   │ Fast    │ Low      │ Syntax only │
│ Type-check         │ Medium  │ Medium   │ Full types  │
│ Analysis           │ Fast    │ Low      │ Depends     │
└────────────────────┴─────────┴──────────┴─────────────┘
```

**Bottleneck:** Type checking (one-time cost)
**Optimization:** Cache type-checked packages

## go/packages: Simplified API

```
┌─────────────────────────────────────────────┐
│          Your Code (Simple)                 │
│  pkgs, _ := packages.Load(cfg, "./...")     │
└─────────────────────────────────────────────┘
                    │
    ┌───────────────┴───────────────┐
    │     go/packages (wrapper)      │
    │  - Handles module resolution   │
    │  - Manages build config        │
    │  - Coordinates components      │
    └───────────────┬───────────────┘
                    │
    ┌───────────────┴────────────────────┐
    │                                    │
    ▼                                    ▼
┌─────────┐                      ┌──────────┐
│go/parser│                      │ go/types │
└─────────┘                      └──────────┘
    │                                    │
    └────────────┬───────────────────────┘
                 ▼
    ┌────────────────────────┐
    │  Fully Resolved Types  │
    └────────────────────────┘
```

**Advantages:**
- One function call vs. many
- Automatic module resolution
- Better error handling
- Recommended for most use cases

## Summary

The architecture consists of three layers:

1. **Parsing Layer** (`go/parser`)
   - Converts source → AST
   - Syntax analysis only

2. **Type Checking Layer** (`go/types`)
   - Converts AST → Resolved Types
   - Semantic analysis

3. **Analysis Layer** (Your Code)
   - Uses resolved types
   - Compares, categorizes, analyzes

**Key Insight:** Type checking bridges the gap between syntax and semantics, enabling accurate type analysis without runtime execution.