(*  Title:      HOL/Subst/UTerm.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Simple term structure for unifiation.
Binary trees with leaves that are constants or variables.
*)

open UTerm;


(**** vars_of lemmas  ****)

goal UTerm.thy "(v : vars_of(Var(w))) = (w=v)";
by (Simp_tac 1);
by (fast_tac HOL_cs 1);
qed "vars_var_iff";

goal UTerm.thy  "(x : vars_of(t)) = (Var(x) <: t | Var(x) = t)";
by (induct_tac "t" 1);
by (ALLGOALS Simp_tac);
by (fast_tac HOL_cs 1);
qed "vars_iff_occseq";


(* Not used, but perhaps useful in other proofs *)
goal UTerm.thy "M<:N --> vars_of(M) <= vars_of(N)";
by (induct_tac "N" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac set_cs 1);
val occs_vars_subset = result();


goal UTerm.thy "vars_of M Un vars_of N <= (vars_of M Un A) Un (vars_of N Un B)";
by (Blast_tac 1);
val monotone_vars_of = result();

goal UTerm.thy "finite(vars_of M)";
by (induct_tac"M" 1);
by (ALLGOALS Simp_tac);
by (forward_tac [finite_UnI] 1);
by (assume_tac 1);
by (Asm_simp_tac 1);
val finite_vars_of = result();
