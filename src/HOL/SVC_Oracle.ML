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
fun svc_tac i st = 
  let val prem = List.nth (prems_of st, i-1)
      val th = invoke_oracle thy "svc_oracle" 
	             (#sign (rep_thm st), Svc.OracleExn prem)
   in 
      compose_tac (false, th, 0) i st
   end 
   handle Svc.OracleExn _ => Seq.empty
	| Subscript       => Seq.empty;


(*True if SVC appears to exist*)
fun svc_enabled() = getenv "SVC_HOME" <> "";
