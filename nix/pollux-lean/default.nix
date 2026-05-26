{
  stdenv,
  lib,
  lean,
  curl,
  cacert,
  git,
  rsync,
  nodejs,
  fetchNpmDeps,
}:
let
  # Only the files that determine the dependency graph. This keeps the FOD
  # hash stable across Pollux source changes — it only changes when
  # lake-manifest.json changes.
  depSrc = lib.cleanSourceWith {
    src = ../../lean;
    filter =
      path: _type:
      builtins.any (suffix: lib.hasSuffix suffix path) [
        "lakefile.toml"
        "lake-manifest.json"
        "lean-toolchain"
      ];
  };

  # Fixed-output derivation: fetch all pre-compiled dependency artifacts.
  #
  # `lake exe cache get` downloads pre-compiled .olean/.ilean files for mathlib
  # and all its transitive dependencies from cache.leanprover.community. Without
  # this, building mathlib from source takes several hours.
  #
  # What we keep in $out (via denylist rsync):
  #   .olean / .ilean   — pre-compiled Lean modules and their trace files
  #   C IR files (ir/)  — Lean-generated C sources (.c); Lake checks for these
  #                       before invoking the Lean compiler. If absent, Lake
  #                       re-runs the compiler even when .olean files are valid,
  #                       adding ~500 ms per module across thousands of modules.
  #                       The .c files use angle-bracket includes and contain no
  #                       Nix store paths. The .setup.json files in ir/ DO embed
  #                       the Lean binary path and are removed by the grep pass.
  #   JS / lake.trace   — ProofWidgets pre-built widget JS and build-trace file.
  #                       lake.trace causes widgetJsAllTarget to skip TypeScript
  #                       recompilation (npm run build) via buildUnlessUpToDate.
  #   Penrose files      — .dsl/.sty/.sub files embedded by mathlib's include_str!
  #                       macros (e.g. CommDiag.lean); required at build time.
  #   Package sources    — Lean source files for each dependency package.
  #
  # What we drop:
  #   .git/   — recreated as minimal stub repos (see below)
  #   bin/    — compiled Lake executables (e.g. the cache binary itself)
  #   *.o / *.a — native object and static library artifacts
  #
  # After the rsync, we scan every file and remove any that contain the local
  # Lean store path (${lean.lean-all}). These are .olean/.ilean files produced
  # when compiling the cache executable from mathlib source rather than
  # downloaded from CDN. Nix rejects FOD outputs that reference store paths.
  #
  # We also reconstruct a minimal git repository for each package. Lake calls
  # `git rev-parse HEAD`, `git remote get-url origin`, and `git diff --quiet HEAD`
  # per dependency. If any of these fail or if diff exits non-zero, Lake treats
  # the package as dirty and bypasses the .olean cache entirely.
  #
  # Lake uses filter clones (--filter=blob:none), so the working tree only
  # contains the files Lake materialized. The pack files in the original clone
  # contain tree objects for every file in the repo (Dockerfiles, CI configs,
  # etc.), so `git diff HEAD` sees all unmaterialized files as deleted → exit 1.
  # Fix: copy the pack files, then run `git read-tree HEAD` to populate the index
  # from HEAD (requires only tree objects, not blobs), then mark every tracked
  # file as --assume-unchanged so git skips the working-tree comparison entirely.
  # Result: git diff --quiet HEAD exits 0 and Lake uses the cached .olean files.
  #
  # dontFixup: stdenv's patchShebangs would rewrite script shebangs to point at
  # the Nix store bash, embedding a store path reference in the FOD output and
  # causing Nix to reject it.
  #
  # To update the hash: set outputHash to lib.fakeHash, run `nix build`, then
  # replace with the hash Nix reports. Must be redone when lake-manifest.json
  # changes (i.e. when any dependency version changes).
  all-deps = stdenv.mkDerivation {
    name = "lean-all-deps";
    src = depSrc;

    outputHash = "sha256-WVWAdJ6EY0Lbb+GzOS2jEcJssawWRyDu+hg4rztRjkI=";
    outputHashMode = "recursive";
    dontFixup = true;

    nativeBuildInputs = [
      lean.lean-all
      curl
      cacert
      git
      rsync
    ];

    buildPhase = ''
      export HOME=$(mktemp -d)
      export SSL_CERT_FILE=${cacert}/etc/ssl/certs/ca-bundle.crt
      lake exe cache get
    '';

    installPhase = ''
      export HOME=$(mktemp -d)

      rsync -a \
        --exclude=".git/" \
        --exclude="bin/" \
        --exclude="*.o" \
        --exclude="*.a" \
        .lake/packages/ $out/

      # Remove any file embedding the local Lean store path. CDN-downloaded
      # .olean files are clean; the culprits are files produced by compiling
      # the cache executable locally (e.g. some .olean/.ilean and ir/.setup.json).
      while IFS= read -r -d "" f; do
        LC_ALL=C grep -qF "${lean.lean-all}" "$f" 2>/dev/null \
          && rm "$f" \
          || true
      done < <(find $out -type f -print0)

      # Reconstruct a minimal git repository for each dependency package so that
      # Lake's git-based cache validity checks pass (see block comment above).
      for pkg_dir in .lake/packages/*/; do
        pkg=$(basename "$pkg_dir")
        [ -d "$pkg_dir/.git" ] || continue

        rev=$(git -C "$pkg_dir" rev-parse HEAD 2>/dev/null) || continue
        [ -n "$rev" ] || continue

        mkdir -p "$out/$pkg/.git/objects/info"
        mkdir -p "$out/$pkg/.git/objects/pack"
        mkdir -p "$out/$pkg/.git/refs/heads"

        # Pack files are content-addressed and deterministic across builds.
        # They contain the commit and tree objects needed by git rev-parse,
        # git read-tree, and git ls-files.
        cp "$pkg_dir/.git/objects/pack/"*.pack "$out/$pkg/.git/objects/pack/" 2>/dev/null || true
        cp "$pkg_dir/.git/objects/pack/"*.idx  "$out/$pkg/.git/objects/pack/" 2>/dev/null || true

        # Copy any loose objects (present in shallow clones).
        find "$pkg_dir/.git/objects" -type f \
          ! -path "*/pack/*" ! -path "*/info/*" \
          | while IFS= read -r obj; do
              rel="''${obj#$pkg_dir/.git/objects/}"
              mkdir -p "$out/$pkg/.git/objects/$(dirname "$rel")"
              cp "$obj" "$out/$pkg/.git/objects/$rel" 2>/dev/null || true
            done

        # Reconstruct config from scratch to avoid copying credential helpers
        # or other settings that might embed Nix store paths.
        origin_url=$(git -C "$pkg_dir" remote get-url origin 2>/dev/null)
        {
          printf '[core]\n\trepositoryformatversion = 0\n\tfilemode = true\n\tbare = false\n'
          printf '[remote "origin"]\n\turl = %s\n\tfetch = +refs/heads/*:refs/remotes/origin/*\n' "$origin_url"
        } > "$out/$pkg/.git/config"

        printf 'ref: refs/heads/main\n' > "$out/$pkg/.git/HEAD"
        printf '%s\n' "$rev" > "$out/$pkg/.git/refs/heads/main"

        # Populate the index from HEAD (tree objects only; no blobs needed) and
        # mark every tracked path as --assume-unchanged. This makes git skip the
        # working-tree comparison: index matches HEAD → git diff --quiet HEAD → 0.
        # Stat fields in the index are zeroed by read-tree, so the index is
        # deterministic across builds.
        git -C "$out/$pkg" read-tree HEAD 2>/dev/null || true
        git -C "$out/$pkg" ls-files -z \
          | xargs -0 git -C "$out/$pkg" update-index --assume-unchanged -- \
          2>/dev/null || true
      done
    '';
  };

  # ProofWidgets source, fetched separately so fetchNpmDeps can be evaluated
  # before all-deps is built (fetchNpmDeps is a Nix evaluation-time operation).
  proofwidgets-src = fetchGit {
    url = "https://github.com/leanprover-community/ProofWidgets4";
    rev = "be3b2e63b1bbf496c478cef98b86972a37c1417d";
    shallow = true;
  };

  # Pre-fetched npm dependencies for ProofWidgets' widgetPackageLock target.
  # Lake runs `npm install` as a prerequisite of widgetJsAll on every build.
  # The TypeScript compilation itself is skipped (lake.trace is in the FOD),
  # but npm install must still succeed offline in the Nix sandbox.
  #
  # To update: set hash to lib.fakeHash, run `nix build`, fill in the hash.
  # Only changes when the proofwidgets rev (above) changes.
  proofwidgets-npm-deps = fetchNpmDeps {
    src = "${proofwidgets-src}/widget";
    hash = "sha256-CzBRrreOSytquZ/xFHPlY8r+lz5Bg9Zk9ienRhc8SiY=";
  };

in
stdenv.mkDerivation {
  pname = "pollux-lean";
  version = "unstable";
  src = ../../lean;

  nativeBuildInputs = [
    lean.lean-all
    git
    nodejs
    rsync
  ];

  configurePhase = ''
    runHook preConfigure

    # git refuses to write to /homeless-shelter (Nix's default HOME).
    export HOME=$(mktemp -d)

    # npm offline mode for the widgetPackageLock target (npm install).
    # Lake runs this as a prerequisite of widgetJsAll on every `lake build`.
    # The TypeScript compilation (npm run build) is skipped because lake.trace
    # is present in the FOD, but npm install still runs and must not need
    # network access.
    export npm_config_cache=${proofwidgets-npm-deps}
    export npm_config_offline=true

    # Restore all pre-fetched packages into .lake/packages. This includes
    # source files, pre-compiled .olean/.ilean files, C IR files, ProofWidgets
    # JS and lake.trace, and minimal git repos — everything Lake needs to build
    # Pollux without recompiling any dependencies.
    mkdir -p .lake
    cp -rP ${all-deps} .lake/packages
    chmod -R +w .lake/packages

    runHook postConfigure
  '';

  buildPhase = ''
    runHook preBuild
    lake build Pollux
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r .lake/build/lib $out/
    runHook postInstall
  '';
}
