(*  Title:      HOL/SVC_Oracle
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1999  University of Cambridge

Installing the oracle for SVC (Stanford Validity Checker)

Based upon the work of Søren T. Heilmann
*)

(*Present the entire subgoal to the oracle, assumptions and all, but possibly
  abstracted.  Use via compose_tac, which performs no lifting but will
  instantiate variables.*)
val svc_tac = SUBGOAL
  (fn (prem,i) => 
   let val (svc_prem, insts) = Svc.abstract prem
       val th = invoke_oracle thy "svc_oracle" 
	             (sign_of thy, Svc.OracleExn svc_prem)

    in compose_tac (false, th, 0) i
    end handle Svc.OracleExn _ => no_tac);


