(*  Title:      HOL/IMP/Natural.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Larry Paulson, TUM
    Copyright   1996 TUM
*)

open Natural;

AddIs evalc.intrs;

val evalc_elim_cases = 
    map evalc.mk_cases
       ["<SKIP,s> -c-> t", 
	"<x:==a,s> -c-> t", 
	"<c1;c2, s> -c-> t",
	"<IF b THEN c1 ELSE c2, s> -c-> t"];

val evalc_WHILE_case = evalc.mk_cases "<WHILE b DO c,s> -c-> t";

AddSEs evalc_elim_cases;

(* evaluation of com is deterministic *)
Goal "<c,s> -c-> t ==> (!u. <c,s> -c-> u --> u=t)";
by (etac evalc.induct 1);
by (thin_tac "<?c,s2> -c-> s1" 7);
(*blast_tac needs Unify.search_bound, trace_bound ::= 40*)
by (ALLGOALS (best_tac (claset() addEs [evalc_WHILE_case])));
qed_spec_mp "com_det";
