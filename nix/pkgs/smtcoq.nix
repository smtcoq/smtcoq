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

  # Arguments
  version ? null,
}:

let
  case = case: out: { inherit case out; };

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
  inherit version;

  owner = "smtcoq";
  pname = "smtcoq";

  opam-name = "rocq-smtcoq";
  useDune = true;

  defaultVersion = lib.switch rocq-core.rocq-version [
    (case (lib.versions.range "9.0" "9.2") "dev")
  ] null;

  release."dev" = {
    src = lib.cleanSource ../..;
    hash = "";
  };

  propagatedBuildInputs = [
    cvc4
    cvc5
    rocq-core.ocamlPackages.num
    trakt
    verit
    zchaff
  ];

  doCheck = true;
  nativeCheckInputs = [ flock ];
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
