{ flake-parts-lib, ... }:
{
  options.perSystem = flake-parts-lib.mkPerSystemOption (
    { lib, ... }: {
      options.polluxPython.packages = lib.mkOption {
        type = lib.types.functionTo (lib.types.listOf lib.types.package);
        default = _ps: [ ];
        description = "Contributions to the shared python environment.";
      };
    }
  );

  config.perSystem = { config, pkgs, ... }: {
    _module.args.python = pkgs.python314;

    polluxPython.packages =
      ps: with ps; [
        python-lsp-server
        numpy
        scipy
        pandas
        pandas-stubs
        polars
        altair
        vl-convert-python
        requests
        rich
      ];

    devShells.eval = pkgs.mkShell {
      buildInputs = with pkgs; [
        gh
        jq
        nushell
        nushellPlugins.polars
        pyright
        (pkgs.python314.withPackages config.polluxPython.packages)
      ];
    };
  };
}
