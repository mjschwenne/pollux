{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/8913c168d1c56dc49a7718685968f38752171c3b";
    flake-utils.url = "github:numtide/flake-utils";
    perennial = {
      # The github fecther doesn't support submodules for some reason...
      url = "git+https://github.com/mit-pdos/perennial.git";
    };
  };

  outputs = {
    nixpkgs,
    flake-utils,
    perennial,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        pollux-go = pkgs.callPackage ./pollux-go {};
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          perennial = perennial.packages.${system}.default;
        };
      in {
        packages = {
          inherit pollux-go rocq-build;
          default = rocq-build;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                # Rocq Deps
                rocq-core
                rocqPackages.stdlib
                coqPackages.equations # And now we can interop these?
                perennial.packages.${system}.default

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
              # OCaml Deps
              ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
                base64
                batteries
                dune_3
                merlin
                findlib
                ocaml
                ocamlbuild
                pprint
                ppx_deriving_yojson
                ppx_expect
                ptime
                qcheck-core
                stdint
                stdio
                utop
                zarith
              ]);

            shellHook = ''
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
            '';
          };
      }
    );
}
