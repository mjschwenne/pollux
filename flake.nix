{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    perennial.url = "github:mit-pdos/perennial";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };
  outputs =
    {
      nixpkgs,
      flake-utils,
      perennial,
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
        inherit (perennial.packages.${system}) perennialPkgs;
        perennial-pkg = perennial.packages.${system}.default;
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          inherit perennialPkgs;
          perennial = perennial-pkg;
        };
        aristotle = pkgs.python313Packages.callPackage ./lean/aristotle.nix { };
      in
      {
        packages = {
          inherit pollux-go rocq-build;
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

              # lean proofwidgets dep
              nodejs-slim

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
            ])
            ++ (with pkgs.lean; [
              lean-all
            ]);

            shellHook = ''
              export ROCQPATH=$COQPATH
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
              export ARISTOTLE_API_KEY=$(cat ../aristotle.txt)
            '';
          };
      }
    );
}
