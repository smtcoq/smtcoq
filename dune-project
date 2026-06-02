(lang dune 3.21)

(using rocq 0.11)

(name rocq-smtcoq)

(generate_opam_files)

(source
 (github smtcoq/smtcoq))

(license CECILL-C)

(authors
 "Michaël Armand"
 "Valentin Blot"
 "Amina Bousalem"
 "Quentin Garchery"
 "Benjamin Grégoire"
 "Chantal Keller"
 "Burak Ekici"
 "Alain Mebsout")

(maintainers
 "Chantal Keller <ckeller@lmf.cnrs.fr>"
 "Vincent Lafeychine <vincent.lafeychine@proton.me>")

(package
 ; Main project
 (name rocq-smtcoq)
 (synopsis
  "A Rocq plugin that checks proof witnesses coming from external SAT and SMT solvers")
 (description
  "- a certified checker for proof witnesses coming from the SAT solver ZChaff and the SMT solvers veriT and CVC4. This checker increases the confidence in these tools by checking their answers a posteriori and allows to import new theroems proved by these solvers in Rocq;\n   - decision procedures through new tactics that discharge some Rocq goals to ZChaff, veriT, CVC4, and their combination\n   ")
 (tags
  ("category:Computer Science/Decision Procedures and Certified Algorithms/Decision procedures"
   "category:Miscellaneous/Coq Extensions"
   "keyword: SMT"
   "keyword: SAT"
   "keyword: automation"
   "logpath:SMTCoq"))
 (depends
  (elpi
   (>= 2.0.7))
  (rocq-elpi
   (>= 2.5.2))
  (rocq-core
   (>= 9.0.0))))

(package
 ; 3rd-party library
 (name alt-ergo))

(package
 ; Standalone LFSC to SMTCoq translator
 (name lfsctosmtcoq)
 (allow_empty))
