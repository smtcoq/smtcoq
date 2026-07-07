{ lib }:

with lib;
{
  mkSMTCoqName =
    {
      smtcoq,
      ...
    }@versions:
    "${mkTraktName versions}-${mkFmt smtcoq.version}";

  mkSMTCoqScope =
    pkgs:
    versions@{
      smtcoq,
      ...
    }:
    (mkTraktScope pkgs versions).overrideScope (
      _: prev: {
        smtcoq = prev.smtcoq.override { version = smtcoq; };
      }
    );

  mkSMTCoq =
    pkgs: versions:
    let
      rocqPackages = mkSMTCoqScope pkgs versions;
    in
    {
      name = "SMTCoq-${mkSMTCoqName rocqPackages}";
      value = rocqPackages.smtcoq;
    };
}
