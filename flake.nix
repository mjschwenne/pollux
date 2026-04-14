{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    perennial.url = "github:mit-pdos/perennial";
    opam-nix.url = "github:tweag/opam-nix";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-rocq-repo = {
      url = "github:rocq-prover/opam";
      flake = false;
    };
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };
  outputs =
    {
      nixpkgs,
      flake-utils,
      perennial,
      opam-nix,
      opam-repository,
      opam-rocq-repo,
      lean4-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfreePredicate =
            pkg:
            builtins.elem (pkgs.lib.getName pkg) [
              "claude-code"
              "claude-agent-acp"
              "aristotlelib"
            ];
          overlays = [ (lean4-nix.readToolchainFile ./lean/lean-toolchain) ];
        };
        pollux-go = pkgs.callPackage ./pollux-go { };
        inherit (opam-nix.lib.${system}) queryToScope;
        scope =
          queryToScope
            {
              repos = [
                "${opam-repository}"
                "${opam-rocq-repo}/released"
              ];
            }
            {
              rocq-equations = "*";
              ocaml-base-compiler = "5.2.1";
            };
        equations = scope.rocq-equations.override {
          inherit (scope) ocaml-base-compiler;
        };
        inherit (perennial.packages.${system}) perennialPkgs;
        perennial-pkg = perennial.packages.${system}.default;
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          inherit equations perennialPkgs;
          perennial = perennial-pkg;
        };
        aristotle = pkgs.python313Packages.callPackage ./lean/aristotle.nix { };
      in
      {
        packages = {
          inherit pollux-go rocq-build equations;
          default = rocq-build;
        };
        devShells.default =
          with pkgs;
          mkShell {
            buildInputs = [
              # Protobuf Deps
              protobuf
              protoc-gen-go
              protoscope
              buf

              # Go deps
              go
              gopls
              pollux-go

              # Misc utilities
              just
              nushell
              gnumake
              xxd

              # eval utilities
              gh
              jq
              (python313.withPackages (
                ps: with ps; [
                  python-lsp-server
                  pyright
                  numpy
                  nptyping
                  scipy
                  pandas
                  pandas-stubs
                  polars
                  altair
                  vl-convert-python
                  requests
                  rich
                  aristotle
                ]
              ))

              # nushell is great for command line polars queries
              nushell
              nushellPlugins.polars

              # nix helpers
              nix-update
              claude-code
              claude-agent-acp
            ]
            ++ (with perennialPkgs; [
              rocq-runtime
              rocq-stdlib
              coq-coqutil
              coq-record-update
              rocq-stdpp
              rocq-iris
              iris-named-props
              perennial-pkg
              equations
            ])
            ++ (with pkgs.lean; [
              lean-all
            ]);

            shellHook = ''
              export ROCQPATH=$COQPATH:${equations}/lib/ocaml/5.2.1/site-lib/coq/user-contrib/
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
              export ARISTOTLE_API_KEY=$(cat ../aristotle.txt)
            '';
          };
      }
    );
}
