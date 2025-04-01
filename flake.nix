{
  description = "A Flake for F* development";

  inputs = {
    nixpkgs.url = "nixpkgs";
    fstar.url = "github:FStarLang/FStar";
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
      in {
        devShells.default = with pkgs;
          mkShell {
            buildInputs = [
              fstar.packages.${system}.fstar
              karamel.packages.${system}.karamel
              just
              protobuf
              protoscope
              buf
              jq
            ];

            shellHook = ''
            '';
          };
      }
    );
}
