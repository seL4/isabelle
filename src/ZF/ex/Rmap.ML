(*  Title:      ZF/ex/Rmap
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Inductive definition of an operator to "map" a relation over a list
*)

open Rmap;

goalw Rmap.thy rmap.defs "!!r s. r<=s ==> rmap(r) <= rmap(s)";
by (rtac lfp_mono 1);
by (REPEAT (rtac rmap.bnd_mono 1));
by (REPEAT (ares_tac ([Sigma_mono, list_mono, domain_mono, range_mono] @ 
                      basic_monos) 1));
qed "rmap_mono";

val Nil_rmap_case = rmap.mk_cases list.con_defs "<Nil,zs> : rmap(r)"
and Cons_rmap_case = rmap.mk_cases list.con_defs "<Cons(x,xs),zs> : rmap(r)";

AddIs  rmap.intrs;
AddSEs [Nil_rmap_case, Cons_rmap_case];

goal Rmap.thy "!!r. r <= A*B ==> rmap(r) <= list(A)*list(B)";
by (rtac (rmap.dom_subset RS subset_trans) 1);
by (REPEAT (ares_tac [domain_rel_subset, range_rel_subset,
                      Sigma_mono, list_mono] 1));
qed "rmap_rel_type";

goal Rmap.thy
    "!!r. A <= domain(r) ==> list(A) <= domain(rmap(r))";
by (rtac subsetI 1);
by (etac list.induct 1);
by (ALLGOALS Fast_tac);
qed "rmap_total";

goalw Rmap.thy [function_def] "!!r. function(r) ==> function(rmap(r))";
by (rtac (impI RS allI RS allI) 1);
by (etac rmap.induct 1);
by (ALLGOALS Fast_tac);
qed "rmap_functional";


(** If f is a function then rmap(f) behaves as expected. **)

goal Rmap.thy "!!f. f: A->B ==> rmap(f): list(A)->list(B)";
by (asm_full_simp_tac 
    (simpset() addsimps [Pi_iff, rmap_rel_type, rmap_functional, rmap_total]) 1);
qed "rmap_fun_type";

goalw Rmap.thy [apply_def] "rmap(f)`Nil = Nil";
by (fast_tac (claset() addIs [the_equality]) 1);
qed "rmap_Nil";

goal Rmap.thy "!!f. [| f: A->B;  x: A;  xs: list(A) |] ==> \
\                   rmap(f) ` Cons(x,xs) = Cons(f`x, rmap(f)`xs)";
by (rtac apply_equality 1);
by (REPEAT (ares_tac ([apply_Pair, rmap_fun_type] @ rmap.intrs) 1));
qed "rmap_Cons";
