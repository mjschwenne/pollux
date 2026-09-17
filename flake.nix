{
  description = "A Flake for Pollux; a Research Project on Data Descriptor Compatilbilty";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    perennial.url = "github:mit-pdos/perennial";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      imports = [
        ({ flake-parts-lib, ... }: {
          options.perSystem = flake-parts-lib.mkPerSystemOption (
            { lib, ... }: {
              options.polluxNixpkgs = {
                overlays = lib.mkOption {
                  type = lib.types.listOf (
                    lib.mkOptionType {
                      name = "nixpkgs-overlay";
                      check = builtins.isFunction;
                      merge = lib.mergeOneOption;
                    }
                  );
                  default = [ ];
                };
                allowUnfreeNames = lib.mkOption {
                  type = lib.types.listOf lib.types.str;
                  default = [ ];
                };
              };
            }
          );
        })

        ./eval/flake-module.nix
        ./lean/flake-module.nix
        ./pollux-go/flake-module.nix
        ./latex/flake-module.nix
        ./rocq/flake-module.nix
      ];

      perSystem =
        {
          config,
          pkgs,
          system,
          lib,
          ...
        }:
        {
          # Configure the nixpkgs instance to use the overlays and unfree packages
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            inherit (config.polluxNixpkgs) overlays;
            config.allowUnfreePredicate =
              pkg: builtins.elem (lib.getName pkg) config.polluxNixpkgs.allowUnfreeNames;
          };

          polluxNixpkgs.allowUnfreeNames = [
            "claude-code"
            "claude-agent-acp"
          ];

          # Output packages from Pollux
          packages = {
            default = config.packages.lean-build;
          };

          devShells.default = pkgs.mkShell {
            buildInputs = with pkgs; [
              # Protobuf Deps
              protobuf
              protoscope
              buf

              # Misc utilities
              just
              gnumake

              # nix helpers
              nix-update

              # AI "helpers"
              claude-code
              claude-agent-acp
            ];

            inputsFrom = [
              config.devShells.lean
              config.devShells.eval
              config.devShells.go
              config.devShells.latex
              config.devShells.rocq
            ];

            # shellHook can't be sharded through inputsFrom, that only grabs buildInputs, not the hooks
            shellHook = ''
              export ROCQPATH=$COQPATH
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
              export ARISTOTLE_API_KEY=$(cat ../aristotle.txt)
            '';
          };
        };
    };
}
