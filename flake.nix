{
  description = "A Flake for F* development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar.url = "github:FStarLang/FStar";
    # pin karamel until nixpkgs can support dune 3.13
    karamel.url = "github:FStarLang/karamel/86f99f08afa04ca792f9c4f64f24db4c0fdbc46c";
    # Use the existing fstar install
    karamel.inputs.fstar.follows = "fstar";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    nixpkgs,
    fstar,
    karamel,
    flake-utils,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        fstar-nixpkgs = import fstar.inputs.nixpkgs {
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
        # Use the fstar nixpkgs to ensure that the ocaml versions align
        everparse-pkg = fstar-nixpkgs.callPackage ./nix/everparse.nix {
          fstar = fstar-pkg;
          karamel = karamel-pkg;
        };
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              fstar-pkg
              karamel-pkg
              everparse-pkg
              just
              protobuf
              protoscope
              buf
              jq
              go
            ];

            shellHook = ''
              export KRML_HOME=${karamel-pkg}
              export EVERPARSE_HOME=${everparse-pkg}
            '';
          };
      }
    );
}
