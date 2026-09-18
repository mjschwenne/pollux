# CLAUDE.md: Go `pollux` CLI

`pollux-go/` is the unverified Go companion to the Lean formalization. It cross-checks the report's wire-format claims against the real protobuf-go implementation and produces the corpus statistics that `eval/` collects. Module `github.com/mjschwenne/pollux`, Go 1.25, a single `pollux` binary (cobra).

## The Report Boundary

Go is evidence, not specification. If Go behavior disagrees with a rule the report states (a varint conversion in `sec:proto-compat-ints`, say), that's a finding for `notes/`. Don't change the Go to agree with the report, or the other way around, without the author. Changes that shift the statistics the report cites (via `eval/`) get a note too.

## Commands

| Command                                        | What it does                                                                                     |
|------------------------------------------------|--------------------------------------------------------------------------------------------------|
| `pollux proto varint`                          | streams integers from stdin through real protobuf-go varint encode/decode between two types (`i32`, `u64`, `s32`, …), to test the report's conversion rules |
| `pollux proto stats <files…>`                  | per-file summary statistics, optionally as Parquet; the source of `eval`'s dataset               |
| `pollux proto recursion <files…>`              | finds self- and mutually-recursive messages (SCCs); the source of the recursion tables           |
| `pollux proto check <old> <new>`               | intended compatibility check; today it only prints order-insensitive descriptor equality (`desclib.FileDescEq`) |
| `pollux json stats <packages>`                 | JSON struct-tag statistics for Go packages                                                       |

`stats` and `recursion` take repeatable `-I`/`--import-path` roots like `protoc`, plus `--parquet <file>`. Run `pollux <cmd> --help` for the rest.

## Layout

| Path                           | Role                                                                                     |
|--------------------------------|------------------------------------------------------------------------------------------|
| `cmd/pollux/main.go`           | cobra command tree                                                                       |
| `protobuf/`                    | `Varint.go`, `Stats.go`, `Parquet.go`, `Recursion.go`, `Check.go` (tree-sitter, via cgo) |
| `internal/desclib/`            | descriptor loading (`bufbuild/protocompile`), recursion analysis (`gograph`), order-insensitive descriptor equality |
| `json/`                        | Go struct JSON-tag statistics (`golang.org/x/tools`)                                     |
| `proto/varint.pb.go`           | **generated** from `varint.proto` by `protoc-gen-go`; don't edit it by hand             |
| `testdata/proto`, `testdata/json` | fixtures, including deliberately non-compiling and recursive schemas                  |

## Build and Test

```bash
nix develop .#go                                   # go, gopls, protoc-gen-go, xxd, and a prebuilt pollux
go build ./... && go test ./...
protoc --go_out=. varint.proto                     # regenerate proto/varint.pb.go (go_package is "./proto")
nix build .#pollux-go                              # from the repo root
```

- **`vendorHash` in `package.nix` must change whenever `go.mod`/`go.sum` do.** The Nix build fails with a hash mismatch that prints the correct value.
- `eval/` calls whatever `pollux` is on `PATH`. The dev shell's copy is the Nix-built package, so `go build` alone does not change what `eval` runs. Rebuild the package and re-enter the shell. Parquet column changes ripple into `eval` (see `eval/CLAUDE.md`).
- Observed 2026-09-18: outside the Go dev shell, `go test ./protobuf` failed with a glibc `undefined symbol: __nptl_change_stack_perm` error, while `internal/desclib` passed. The package links tree-sitter through cgo, so a Go/C toolchain mismatch between shells is the likely cause. Try the Go dev shell before debugging code.
