(*  Title:      HOL/ex/Recdefs.ML
    ID:         $Id$
    Author:     Konrad Lawrence C Paulson
    Copyright   1997  University of Cambridge

A few proofs to demonstrate the functions defined in Recdefs.thy
Lemma statements from Konrad Slind's Web site
*)

Addsimps qsort.rules;

Goal "(x: set (qsort (ord,l))) = (x: set l)";
by (res_inst_tac [("u","ord"),("v","l")] qsort.induct 1);
by Auto_tac;
qed "qsort_mem_stable";


(** The silly g function: example of nested recursion **)

Addsimps g.rules;

Goal "g x < Suc x";
by (res_inst_tac [("u","x")] g.induct 1);
by Auto_tac;
qed "g_terminates";

Goal "g x = 0";
by (res_inst_tac [("u","x")] g.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [g_terminates])));
qed "g_zero";

(*** the contrived `mapf' ***)

(* proving the termination condition: *)
val [tc] = mapf.tcs;
goalw_cterm [] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop tc));
by (rtac allI 1);
by (case_tac "n=0" 1);
by (ALLGOALS Asm_simp_tac);
val lemma = result();

(* removing the termination condition from the generated thms: *)
val [mapf_0,mapf_Suc] = mapf.rules;
val mapf_Suc = lemma RS mapf_Suc;

val mapf_induct = lemma RS mapf.induct;
