{ ... }:
{
  perSystem =
    { pkgs, ... }:
    let
      pollux-go = pkgs.callPackage ./package.nix { };
    in
    {
      packages.pollux-go = pollux-go;

      devShells.go = pkgs.mkShell {
        buildInputs = with pkgs; [
          go
          gopls
          protoc-gen-go
          xxd

          pollux-go
        ];
      };
    };
}
