let
  mkRocqPackages =
    base:
    base.overrideScope (
      final: _: {
        smtcoq = final.callPackage ./smtcoq.nix { };
      }
    );
in
final: prev: {
  rocqPackages = mkRocqPackages (prev.rocqPackages or { });

  rocqPackages_9_0 = mkRocqPackages (prev.rocqPackages_9_0 or { });
  rocqPackages_9_1 = mkRocqPackages (prev.rocqPackages_9_1 or { });
  rocqPackages_9_2 = mkRocqPackages (prev.rocqPackages_9_2 or { });

  verit = final.callPackage ./verit.nix { inherit (prev) verit; };
  zchaff = final.callPackage ./zchaff.nix { inherit (prev) zchaff; };
}
