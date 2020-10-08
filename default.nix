{ nixpkgs ? import nix/nixpkgs.nix {} }:

let lib = nixpkgs.lib;
    filterHaskellSource = src:
      builtins.filterSource (path: type:
        lib.all (i: i != baseNameOf path)
        [ ".git" "dist-newstyle" "cabal.project.local" "nix"
          "dist" ".stack-work" ".DS_Store" "default.nix" "shell.nix" "result"
        ]
          && lib.all (i: !(lib.hasSuffix i path)) [ ".lkshf" ]
          && lib.all
              (i: !(lib.hasPrefix i (baseNameOf path)))
              [ "cabal.project.local" ".ghc.environment." ]
        ) src;

in nixpkgs.haskellPackages.callCabal2nix "circuit-notation" (filterHaskellSource ./.) {}
