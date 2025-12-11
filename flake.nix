{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/f61125a668a320878494449750330ca58b78c557";
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
  };
  outputs = {
    nixpkgs,
    flake-utils,
    perennial,
    opam-nix,
    opam-repository,
    opam-rocq-repo,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        pollux-go = pkgs.callPackage ./pollux-go {};
        inherit (perennial.packages.${system}) perennialPkgs;
        perennial-pkg = perennial.packages.${system}.default;
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          perennial = perennial-pkg;
        };
        inherit (opam-nix.lib.${system}) queryToScope;
        equations =
          (queryToScope {
              repos = [
                "${opam-repository}"
                "${opam-rocq-repo}/released"
              ];
            }
            {
              rocq-equations = "*";
            }).rocq-equations;
      in {
        packages = {
          inherit pollux-go rocq-build equations;
          default = rocq-build;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
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
                (python313.withPackages (ps:
                  with ps; [
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
                  ]))

                # nushell is great for command line polars queries
                nushell
                nushellPlugins.polars

                # nix helpers
                nix-update
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
              ]);

            shellHook = ''
              export ROCQPATH=$COQPATH:${equations}/lib/ocaml/5.2.1/site-lib/coq/user-contrib/
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
            '';
          };
      }
    );
}
