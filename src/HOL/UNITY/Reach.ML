(*  Title:      HOL/UNITY/Reach.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Reachability in Directed Graphs.  From Chandy and Misra, section 6.4.
	[ this example took only four days!]
*)

(*TO SIMPDATA.ML??  FOR CLASET??  *)
val major::prems = goal thy 
    "[| if P then Q else R;    \
\       [| P;   Q |] ==> S;    \
\       [| ~ P; R |] ==> S |] ==> S";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addSDs [if_bool_eq_disj RS iffD1] addIs prems) 1);
qed "ifE";

AddSEs [ifE];


Addsimps [Rprg_def RS def_prg_Init];
program_defs_ref := [Rprg_def];

Addsimps [simp_of_act asgt_def];

(*All vertex sets are finite*)
AddIffs [[subset_UNIV, finite_graph] MRS finite_subset];

Addsimps [simp_of_set reach_invariant_def];

Goal "Rprg : Always reach_invariant";
by (always_tac 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "reach_invariant";


(*** Fixedpoint ***)

(*If it reaches a fixedpoint, it has found a solution*)
Goalw [fixedpoint_def]
     "fixedpoint Int reach_invariant = { %v. (init, v) : edges^* }";
by (rtac equalityI 1);
by (auto_tac (claset() addSIs [ext], simpset()));
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 2);
by (etac rtrancl_induct 1);
by Auto_tac;
qed "fixedpoint_invariant_correct";

Goalw [FP_def, fixedpoint_def, stable_def, constrains_def, Rprg_def]
     "FP Rprg <= fixedpoint";
by Auto_tac;
by (dtac bspec 1 THEN atac 1);
by (asm_full_simp_tac (simpset() addsimps [Image_singleton, image_iff]) 1);
by (dtac fun_cong 1);
by Auto_tac;
val lemma1 = result();

Goalw [FP_def, fixedpoint_def, stable_def, constrains_def, Rprg_def]
     "fixedpoint <= FP Rprg";
by (auto_tac (claset() addSIs [ext], simpset()));
val lemma2 = result();

Goal "FP Rprg = fixedpoint";
by (rtac ([lemma1,lemma2] MRS equalityI) 1);
qed "FP_fixedpoint";


(*If we haven't reached a fixedpoint then there is some edge for which u but
  not v holds.  Progress will be proved via an ENSURES assertion that the
  metric will decrease for each suitable edge.  A union over all edges proves
  a LEADSTO assertion that the metric decreases if we are not at a fixedpoint.
  *)

Goal "- fixedpoint = (UN (u,v): edges. {s. s u & ~ s v})";
by (simp_tac (simpset() addsimps
	      ([Compl_FP, UN_UN_flatten, FP_fixedpoint RS sym, Rprg_def])) 1);
by Auto_tac;
 by (ALLGOALS (dtac bspec THEN' atac));
 by (rtac fun_upd_idem 1);
 by (auto_tac (claset(),simpset() addsimps [fun_upd_idem_iff]));
qed "Compl_fixedpoint";

Goal "A - fixedpoint = (UN (u,v): edges. A Int {s. s u & ~ s v})";
by (simp_tac (simpset() addsimps [Diff_eq, Compl_fixedpoint]) 1);
by (Blast_tac 1);
qed "Diff_fixedpoint";


(*** Progress ***)

Goalw [metric_def] "~ s x ==> Suc (metric (s(x:=True))) = metric s";
by (subgoal_tac "{v. ~ (s(x:=True)) v} = {v. ~ s v} - {x}" 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [card_Suc_Diff1]) 1);
qed "Suc_metric";

Goal "~ s x ==> metric (s(x:=True)) < metric s";
by (etac (Suc_metric RS subst) 1);
by (Blast_tac 1);
qed "metric_less";
AddSIs [metric_less];

Goal "metric (s(y:=s x | s y)) <= metric s";
by (case_tac "s x --> s y" 1);
by (auto_tac (claset() addIs [less_imp_le],
	      simpset() addsimps [fun_upd_idem]));
qed "metric_le";

Goal "Rprg : ((metric-``{m}) - fixedpoint) LeadsTo (metric-``(lessThan m))";
by (simp_tac (simpset() addsimps [Diff_fixedpoint]) 1);
by (rtac LeadsTo_UN 1);
by Auto_tac;
by (ensures_tac "asgt a b" 1);
by (Blast_tac 2);
by (full_simp_tac (simpset() addsimps [not_less_iff_le]) 1);
by (dtac (metric_le RS order_antisym) 1);
by (auto_tac (claset() addEs [less_not_refl3 RSN (2, rev_notE)],
	      simpset()));
qed "LeadsTo_Diff_fixedpoint";

Goal "Rprg : (metric-``{m}) LeadsTo (metric-``(lessThan m) Un fixedpoint)";
by (rtac ([LeadsTo_Diff_fixedpoint RS LeadsTo_weaken_R,
	   subset_imp_LeadsTo] MRS LeadsTo_Diff) 1);
by Auto_tac;
qed "LeadsTo_Un_fixedpoint";


(*Execution in any state leads to a fixedpoint (i.e. can terminate)*)
Goal "Rprg : UNIV LeadsTo fixedpoint";
by (rtac LessThan_induct 1);
by Auto_tac;
by (rtac LeadsTo_Un_fixedpoint 1);
qed "LeadsTo_fixedpoint";

Goal "Rprg : UNIV LeadsTo { %v. (init, v) : edges^* }";
by (stac (fixedpoint_invariant_correct RS sym) 1);
by (rtac ([reach_invariant, LeadsTo_fixedpoint] 
	  MRS Always_LeadsTo_weaken) 1); 
by Auto_tac;
qed "LeadsTo_correct";
