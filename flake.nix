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
        varint_conversion = pkgs.callPackage ./varint_conversion {};
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          perennial = perennial.packages.${system}.default;
        };
      in {
        packages = {
          inherit varint_conversion rocq-build;
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
                varint_conversion

                # Misc utilities
                just
                gnumake
                xxd

                # eval utilities
                gh
                jq
                python3
                python313Packages.python-lsp-server
                pyright
                python313Packages.altair
                python313Packages.vl-convert-python
                python313Packages.requests
                python313Packages.rich

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
