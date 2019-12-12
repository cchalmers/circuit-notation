{ nixpkgs ? import <nixpkgs> {}
}:

with nixpkgs;

stdenv.mkDerivation {
  name = "circuit-notation-env";

  buildInputs = [
    ghc
    cabal-install
    ghcid
  ];
}
