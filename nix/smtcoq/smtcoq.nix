{
  # Libraries
  lib,
  mkRocqDerivation,
  stdenv,

  # Dependencies
  cvc4,
  cvc5,
  flock,
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
mkRocqDerivation rec {
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

  doCheck = true;

  checkInputs = [ flock ];
  checkPhase = ''
    runHook preCheck
    patchShebangs ./unit-tests/files/run_zchaff.sh
    dune runtest -p ${opam-name} ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
    runHook postCheck
  '';

  passthru = { inherit lfsc-sigs; };

  meta = {
    description = "A Rocq plugin that checks proof witnesses coming from external SAT and SMT solvers";
    homepage = "https://github.com/smtcoq/smtcoq";
    license = lib.licenses.cecill-c;
  };
}
