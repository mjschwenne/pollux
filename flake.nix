{
  description = "A Flake for F* and Pollux development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar.url = "github:FStarLang/FStar";
    # pin karamel until nixpkgs can support dune 3.13
    karamel.url = "github:FStarLang/karamel/86f99f08afa04ca792f9c4f64f24db4c0fdbc46c";
    # Use the existing fstar install
    karamel.inputs.fstar.follows = "fstar";
    # Use my nix flake for everparse
    everparse.url = "github:mjschwenne/everparse/nix";
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
        everparse-pkg = everparse.packages."${system}".default;
        dir-locals = pkgs.callPackage ./nix/dir-locals.nix {
          karamel = karamel-pkg;
          everparse = everparse-pkg;
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
              dir-locals
            ];

            shellHook = ''
              export KRML_HOME=${karamel-pkg}
              export EVERPARSE_HOME=${everparse-pkg}
              export DIR_LOCALS=${dir-locals}
              ln -f -s ${dir-locals}/dir-locals.el .dir-locals.el
            '';
          };
      }
    );
}
