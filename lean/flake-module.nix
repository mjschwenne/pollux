{ inputs, ... }:
{
  perSystem = { pkgs, python, ... }: {
    polluxNixpkgs.overlays = [ (inputs.lean4-nix.readToolchainFile ./lean-toolchain) ];
    polluxNixpkgs.allowUnfreeNames = [ "aristotlelib" ];

    packages.lean-build = pkgs.callPackage ./package.nix { };
    polluxPython.packages = _ps: [ (python.pkgs.callPackage ./aristotle.nix { }) ];

    devShells.lean = pkgs.mkShell {
      buildInputs = with pkgs; [
        lean.lean-all
        # lean proofwidgets dep
        nodejs-slim
      ];
    };
  };
}
