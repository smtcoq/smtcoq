{
  inputs = {
    trakt.url = "github:rocq-trakt/trakt";

    nixpkgs.follows = "trakt/nixpkgs";
    flake-parts.follows = "trakt/flake-parts";
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      self,
      trakt,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      flake = {
        overlays = {
          smtcoq = import ./nix/smtcoq;

          default = nixpkgs.lib.composeManyExtensions [
            trakt.overlays.default
            self.overlays.smtcoq
          ];
        };
      };

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };

          formatter = pkgs.nixfmt-tree;

          packages = rec {
            inherit (pkgs) cvc4 cvc5 verit zchaff;
            inherit (pkgs.rocqPackages) smtcoq;

            default = smtcoq;
          };

          devShells.default = pkgs.mkShell {
            inputsFrom = [ pkgs.rocqPackages.smtcoq ];

            LFSCSIGS = "${pkgs.rocqPackages.smtcoq.passthru.lfsc-sigs}";
          };
        };
    };
}
