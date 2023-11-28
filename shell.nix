{ nixpkgs ? import nix/nixpkgs.nix {}
}:

with nixpkgs;

stdenv.mkDerivation {
  name = "circuit-notation-env";

  buildInputs = [
    ghc
    # cabal-install
    # haskellPackages.ghcid
    haskellPackages.stylish-haskell
  ];

  shellHook = ''
    test() {
      ghcid --reverse-errors --no-height-limit --clear \
        --reload example --reload src \
        -c "cabal repl" \
        "$@"
    }
    >&2 echo 'Added test command. Usage: test -T ":l example/Testing.hs"'
    '';
}
