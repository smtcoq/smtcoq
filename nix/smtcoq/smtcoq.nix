{
  # Libraries
  lib,
  mkRocqDerivation,
  stdenv,

  # Dependencies
  cvc4,
  cvc5,
  rocq-core,
  rocq-elpi,
  stdlib,
  trakt,
  verit,
  zchaff,
}:

let
  lfsc-sigs = stdenv.mkDerivation {
    name = "lfsc-sigs";
    src = ../../src/lfsc/signatures;

    postInstall = ''
      mkdir $out
      cp -rv . $out
    '';
  };
in
mkRocqDerivation {
  pname = "smtcoq";

  src = ../..;
  version = "dev";

  opam-name = "rocq-smtcoq";
  useDune = true;

  propagatedBuildInputs = [
    rocq-elpi
    stdlib
    trakt
  ];

  buildInputs = [
    cvc4
    cvc5
    rocq-core.ocamlPackages.num
    verit
    zchaff
  ];

  passthru = { inherit lfsc-sigs; };

  meta = {
    description = "A Rocq plugin that checks proof witnesses coming from external SAT and SMT solvers";
    homepage = "https://github.com/smtcoq/smtcoq";
    license = lib.licenses.cecill-c;
  };
}
