# default recipe
default:
    @just --list

buf-lint version:
    buf lint ./proto/v{{version}}/ledger.proto

buf-breaking new old:
    buf breaking ./proto/v{{new}}/ledger.proto --against ./proto/v{{old}}/ledger.proto
