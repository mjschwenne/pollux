{
  description = "A Flake for F* and Pollux development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar.url = "github:FStarLang/FStar";
    karamel.url = "github:FStarLang/karamel";
    # Use the existing fstar install
    karamel.inputs.fstar.follows = "fstar";
    # Use my nix flake for everparse
    everparse.url = "github:mjschwenne/everparse/nix";
    everparse.inputs.fstar.follows = "fstar";
    everparse.inputs.karamel.follows = "karamel";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    nixpkgs,
    fstar,
    karamel,
    everparse,
    flake-utils,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        fstar-pkg = fstar.packages.${system}.fstar;
        karamel-pkg = karamel.packages.${system}.karamel.overrideAttrs {
          # So karamel correctly exports everything it needs to,
          # but everparse expects a different export structure.
          #
          # This patch changes the lib export to be krmllib and
          # places an extra copy of the binary executable at
          # $out/krml rather than $out/bin/krml where nix wants it
          patches = [./nix/karamel-install.patch];
        };
        varint_conversion = pkgs.callPackage ./nix/pollux_varint_conversion.nix {};
        everparse-pkg = everparse.packages."${system}".default;
        ocaml-protoc-plugin = pkgs.callPackage ./nix/ocaml-protoc-plugin.nix {
          buildDunePackage = pkgs.ocaml-ng.ocamlPackages_4_14.buildDunePackage;
          ocaml = pkgs.ocaml-ng.ocamlPackages_4_14.ocaml;
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        };
        dir-locals = pkgs.callPackage ./nix/dir-locals.nix {
          karamel = karamel-pkg;
          everparse = everparse-pkg;
        };
        pollux = pkgs.callPackage ./nix/pollux.nix {
          inherit fstar ocaml-protoc-plugin varint_conversion;
        };
      in {
        packages = {
          inherit pollux;
          default = pollux;
          github-cache.fstar = fstar-pkg;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                fstar-pkg
                karamel-pkg
                everparse-pkg
                just
                protobuf
                protoscope
                buf
                xxd
                go
                ocaml-protoc-plugin
                protoc-gen-go
                dir-locals
                varint_conversion

                nix-update
              ]
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

            dontDetectOcamlConflicts = true;

            shellHook = ''
              export FSTAR_HOME=${fstar-pkg}
              export KRML_HOME=${karamel-pkg}
              export EVERPARSE_HOME=${everparse-pkg}
              export OCAMLPATH=$OCAMLPATH:${fstar-pkg}/lib
              export DIR_LOCALS=${dir-locals}
              ln -f -s ${dir-locals}/dir-locals.el .dir-locals.el
            '';
          };
      }
    );
}
