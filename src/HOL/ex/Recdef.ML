(*  Title:      HOL/ex/Recdef.ML
    ID:         $Id$
    Author:     Konrad Lawrence C Paulson
    Copyright   1997  University of Cambridge

A few proofs to demonstrate the functions defined in Recdef.thy
Lemma statements from Konrad Slind's Web site
*)

open Recdef;

Addsimps qsort.rules;

goal thy "(x mem qsort (ord,l)) = (x mem l)";
by (res_inst_tac [("u","ord"),("v","l")] qsort.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac[expand_if])));
by (Blast_tac 1);
qed "qsort_mem_stable";


(** The silly g function: example of nested recursion **)

Addsimps g.rules;

goal thy "g x < Suc x";
by (res_inst_tac [("u","x")] g.induct 1);
by (Auto_tac());
by (trans_tac 1);
qed "g_terminates";

goal thy "g x = 0";
by (res_inst_tac [("u","x")] g.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [g_terminates])));
qed "g_zero";

