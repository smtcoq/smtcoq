(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


module MakeCnf :
  functor (Form : SmtForm.FORM) ->
    sig
      val make_cnf :
        SmtTrace.trace_state -> Form.reify -> Form.t SmtCertif.clause -> Form.t SmtCertif.clause
    end
