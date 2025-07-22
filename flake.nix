{ 
  description = "A flake for developing & using circuit-notation";
  inputs = {
    clash-compiler.url = "github:clash-lang/clash-compiler";
  };
  outputs = { self, flake-utils, clash-compiler, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        # What version of the GHC compiler to use
        compiler-version = "ghc910";

        pkgs = (import clash-compiler.inputs.nixpkgs {
          inherit system;
        }).extend clash-compiler.overlays.${compiler-version};
        clash-pkgs = pkgs."clashPackages-${compiler-version}";

        overlay = final: prev: {
          circuit-notation = prev.developPackage {
            root = ./.;
            overrides = _: _: final;
          };
        };

        hs-pkgs = clash-pkgs.extend overlay;
      in
      {
        # Expose the overlay which adds circuit-notation
        # The base of the overlay is clash-pkgs
        overlay = overlay;

        devShells.default = hs-pkgs.shellFor {
          packages = p: [
            p.circuit-notation
          ];

          nativeBuildInputs = 
            [
              # Haskell stuff
              hs-pkgs.cabal-install
              hs-pkgs.cabal-plan
              hs-pkgs.haskell-language-server
              hs-pkgs.fourmolu
            ]
          ;
        };
        packages = {
          circuit-notation = hs-pkgs.circuit-notation;

          default = hs-pkgs.circuit-notation;
        };
      });
}
