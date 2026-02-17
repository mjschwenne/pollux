# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Pollux is a formally verified Protocol Buffers parser and serializer implementation written in Rocq (formerly Coq). The project proves correctness properties about protobuf parsing using dependent types and formal verification.

## Build System and Commands

### Primary Build Commands

The project uses Nix as the primary build system:

```bash
# Build the entire project (Rocq proofs)
nix build

# Enter development shell with all dependencies
nix develop
```

### Building Rocq Proofs

Inside the development shell or with proper environment setup:

```bash
# Build all .vo files (compiled proofs)
make vo

# Build .vos files (quick compilation without proofs)
make vos

# Build .vok files (proof checking only)
make vok

# Clean build artifacts
make clean
```

### Testing and Linting (Protobuf)

Using `just` for protobuf-related tasks:

```bash
# Lint a specific proto version
just buf-lint 5

# Check breaking changes between versions
just buf-breaking 5 4
```

### Go Implementation

The `pollux-go` directory contains a Go reference implementation:

```bash
cd pollux-go
go build ./...
go test ./...
```

### OCaml Extracted Code

The `ocaml` directory contains OCaml code extracted from the Rocq proofs:

```bash
cd ocaml
dune build
dune test
```

## Architecture

### Rocq/Coq Proof Structure (`src/`)

The formal verification is organized into layers of abstraction:

1. **Abstract Parser Infrastructure** (`src/parse/`)
   - `Input.v`: Abstract input interface using module functors, defines operations on input sequences
   - `Failure.v`: Error handling for parsers
   - `Parser.v`: Core parser combinators (Success/Failure, monadic operations)
   - `Serializer.v`: Dual serialization combinators
   - `Theorems.v`: Correctness proofs about parser/serializer composition

2. **Foundation** (`src/`)
   - `Prelude.v`: Common imports and notations (lists, integers, stdpp, Perennial helpers)
   - `Varint.v`: Variable-length integer encoding/decoding (core protobuf primitive)
   - `Descriptors.v`: Protobuf schema descriptors (field types, message descriptors, mutually recursive definitions)

3. **Protocol Buffers Implementation**
   - `ProtoParse.v`: Main protobuf parser using the abstract parser framework, instantiated with `ByteInput`
   - `Parse.v`: Earlier/alternative parsing implementation
   - `SimplParse.v`: Simplified parsing examples
   - `InterParse.v`: Intermediate parsing layer

The architecture uses **module functors** extensively: `Parsers(InputModule)` and `Serializers(InputModule)` are functors that abstract over the input type, allowing the same parsing logic to work with different input representations.

### Key Abstraction: Width-Indexed Integer Operations

Functions like `uint_change_w`, `int_change_w`, `sint_change_w` in `Parse.v` and `ProtoParse.v` handle integer conversions between different protobuf wire formats (varint, zigzag, fixed-width) with width parameters (32 or 64 bits). These are proven correct against the official protobuf implementation.

### Dependencies

The project heavily depends on:
- **Perennial**: Verification framework (provides word/integer helpers, little-endian operations)
- **Equations**: Plugin for defining complex recursive functions
- **Iris**: Separation logic framework (via stdpp for gmaps/mapsets)
- **rocq-stdpp**: Standard library with decidable equality, finite maps/sets

### Protobuf Schema Evolution (`proto/`)

The `proto/` directory contains multiple versions (v1-v5) of the ledger protobuf schema, demonstrating schema evolution. The `buf.yaml` configuration and `just` commands help verify backward compatibility between versions.

### Multi-Language Strategy

- **Rocq** (`src/`): Formal specification and proofs of correctness
- **OCaml** (`ocaml/`): Extracted executable code from Rocq proofs
- **Go** (`pollux-go/`): Reference implementation for testing and validation

## Development Workflow

### Working with Rocq Proofs

1. Make changes to `.v` files in `src/`
2. Rebuild dependencies: `make .rocqdeps.d`
3. Compile specific file: `rocq compile -Q src Pollux src/YourFile.v`
4. Or rebuild all: `make vo`

### Understanding Build Artifacts

- `.vo` files: Fully compiled and checked proofs
- `.vos` files: Quick compilation without proof checking (useful for development)
- `.vok` files: Only proof checking
- `.glob` files: Symbol information for documentation
- `.rocqdeps.d`: Automatically generated dependency information

### Rocq Path Configuration

The project uses `-Q src Pollux` (see `_RocqProject`), meaning files in `src/` are imported with the `Pollux` prefix:

```coq
From Pollux Require Import Prelude.
From Pollux.parse Require Import Parser.
```

### CI/CD

The `.github/workflows/ci.yml` runs `nix build -L` on both Linux and macOS, which compiles all Rocq proofs and ensures they type-check.
