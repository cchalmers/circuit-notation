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

    haskellPackages =
      nixpkgs.haskellPackages.extend (super: self:
      {
        ghc-lib = self.callHackageDirect {
          pkg = "ghc-lib";
          ver = "8.10.2.20200916";
          sha256 = "1gx0ijay9chachmd1fbb61md3zlvj24kk63fk3dssx8r9c2yp493";
        } {};

        ghc-lib-parser = self.callHackageDirect {
          pkg = "ghc-lib-parser";
          ver = "8.10.2.20200916";
          sha256 = "1apm9zn484sm6b8flbh6a2kqnv1wjan4l58b81cic5fc1jsqnyjk";
        } {};

      });

in haskellPackages.callCabal2nix "circuit-notation" (filterHaskellSource ./.) {}
