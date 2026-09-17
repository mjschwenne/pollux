{ inputs, ... }:
{
  perSystem =
    { pkgs, inputs', ... }:
    let
      inherit (inputs'.perennial.packages) perennialPkgs;
      perennial-pkg = inputs'.perennial.packages.default;
    in
    {
      packages.rocq-build = pkgs.callPackage ./package.nix {
        inherit perennialPkgs;
        perennial = perennial-pkg;
      };

      devShells.rocq = pkgs.mkShell {
        buildInputs = with perennialPkgs; [
          rocq-runtime
          rocq-stdlib
          coq-coqutil
          coq-record-update
          rocq-stdpp
          rocq-iris
          iris-named-props
          perennial-pkg
        ];
      };
    };
}
