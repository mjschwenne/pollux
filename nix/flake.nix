{
  description = "A Flake for F* development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar.url = "github:FStarLang/FStar/8080c2c10e2a15fdacea6df31f0921850294cd37";
    karamel.url = "github:FStarLang/karamel/86f99f08afa04ca792f9c4f64f24db4c0fdbc46c";
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
        fstarp = fstar.packages.${system}.fstar;
        karamelp = karamel.packages.${system}.karamel;
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              fstarp
              karamel.packages.${system}.karamel
              (callPackage ./everparse.nix {
                fstar = fstarp;
                karamel = karamelp;
                version = "v2025.04.01";
              })
            ];

            shellHook = ''
            '';
          };
      }
    );
}
