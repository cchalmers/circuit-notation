{ nixpkgs ? import nix/nixpkgs.nix {}
}:

with nixpkgs;

stdenv.mkDerivation {
  name = "circuit-notation-env";

  buildInputs = [
    ghc
    cabal-install
    haskellPackages.ghcid
  ];
}
