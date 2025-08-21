{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/a595dde4d0d31606e19dcec73db02279db59d201";
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
        flocq = pkgs.callPackage ./nix/flocq {};
      in {
        packages = {
          inherit varint_conversion;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                # Rocq Deps
                rocq-core
                rocqPackages.stdlib
                perennial.packages.${system}.default
                flocq

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
            '';
          };
      }
    );
}
