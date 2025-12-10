{
  description = "A Flake for Pollux development in Rocq";

  inputs = {
    nixpkgs.url = "github:/NixOS/nixpkgs/f61125a668a320878494449750330ca58b78c557";
    flake-utils.url = "github:numtide/flake-utils";
    perennial.url = "github:mit-pdos/perennial";
  };

  outputs = {
    nixpkgs,
    flake-utils,
    perennial,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
        };
        pollux-go = pkgs.callPackage ./pollux-go {};
        rocq-build = pkgs.callPackage ./nix/pollux-rocq {
          perennial = perennial.packages.${system}.default;
        };
        inherit (perennial.packages.${system}) perennialPkgs;
      in {
        packages = {
          inherit pollux-go rocq-build;
          default = rocq-build;
        };
        devShells.default = with pkgs;
          mkShell {
            buildInputs =
              [
                coqPackages.equations # And now we can interop these?

                # Protobuf Deps
                protobuf
                protoc-gen-go
                protoscope
                buf

                # Go deps
                go
                gopls
                pollux-go

                # Misc utilities
                just
                nushell
                gnumake
                xxd

                # eval utilities
                gh
                jq
                (python313.withPackages (ps:
                  with ps; [
                    python-lsp-server
                    pyright
                    numpy
                    nptyping
                    scipy
                    pandas
                    pandas-stubs
                    polars
                    altair
                    vl-convert-python
                    requests
                    rich
                  ]))

                # nushell is great for command line polars queries
                nushell
                nushellPlugins.polars

                # nix helpers
                nix-update
              ]
              ++ (with perennialPkgs; [
                rocq-runtime
                rocq-stdlib
                coq-coqutil
                coq-record-update
                rocq-stdpp
                rocq-iris
                iris-named-props
                perennial.packages.${system}.default
              ]);

            shellHook = ''
              export ROCQPATH=$COQPATH
              unset COQPATH
              export GITHUB_TOKEN=$(cat ../gh_pat.txt)
            '';
          };
      }
    );
}
