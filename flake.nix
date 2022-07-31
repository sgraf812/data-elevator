# SPDX-FileCopyrightText: 2021 Serokell <https://serokell.io/>
#
# SPDX-License-Identifier: CC0-1.0

{
  description = "data-elevator";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        #haskellPackages = pkgs.haskellPackages;
        haskellPackages = pkgs.haskell.packages.ghc923;

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        # DON'T FORGET TO PUT YOUR PACKAGE NAME HERE, REMOVING `throw`
        packageName = "data-elevator";
      in {
        packages.${packageName} =
          haskellPackages.callCabal2nix packageName self rec {
            # Dependency overrides go here
          };

        defaultPackage = self.packages.${system}.${packageName};

        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            haskellPackages.haskell-language-server # you must build it with your ghc to work
            cabal-install
          ];
          inputsFrom = builtins.attrValues self.packages.${system};
        };
      });
}
