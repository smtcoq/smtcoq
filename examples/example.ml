let _ = Printf.printf "Zchaff_checker.checker \"sat.cnf\" \"sat.log\" = %b\n" (Zchaff_checker.checker "sat.cnf" "sat.log")
let _ = Printf.printf "Zchaff_checker.checker \"hole4.cnf\" \"hole4.log\" = %b\n" (Zchaff_checker.checker "hole4.cnf" "hole4.log")




let _ = Printf.printf "Verit_checker.checker \"euf.smt2\" \"euf.log\" = %b\n" (Verit_checker.checker "euf.smt2" "euf.log")
