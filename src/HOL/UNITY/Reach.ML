(*  Title:      HOL/UNITY/Reach.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Reachability in Directed Graphs.  From Chandy and Misra, section 6.4.
*)

open Reach;

(*TO SIMPDATA.ML??  FOR CLASET??  *)
val major::prems = goal thy 
    "[| if P then Q else R;    \
\       [| P;   Q |] ==> S;    \
\       [| ~ P; R |] ==> S |] ==> S";
by (cut_facts_tac [major] 1);
by (blast_tac (claset() addSDs [if_bool_eq_disj RS iffD1] addIs prems) 1);
qed "ifE";

AddSEs [ifE];


val cmd_defs = [racts_def, asgt_def, update_def];

goalw thy [racts_def] "id : racts";
by (Simp_tac 1);
qed "id_in_racts";
AddIffs [id_in_racts];

(*All vertex sets are finite*)
AddIffs [[subset_UNIV, finite_graph] MRS finite_subset];


(** Constrains/Ensures tactics: NEED TO BE GENERALIZED OVER ALL PROGRAMS **)

(*proves "constrains" properties when the program is specified*)
val constrains_tac = 
   SELECT_GOAL
      (EVERY [rtac constrainsI 1,
	      rewtac racts_def,
	      REPEAT_FIRST (eresolve_tac [insertE, emptyE]),
	      rewrite_goals_tac [racts_def, asgt_def],
	      ALLGOALS (SELECT_GOAL Auto_tac)]);


(*proves "ensures" properties when the program is specified*)
fun ensures_tac sact = 
    SELECT_GOAL
      (EVERY [REPEAT (resolve_tac [LeadsTo_Basis, leadsTo_Basis, ensuresI] 1),
	      res_inst_tac [("act", sact)] transient_mem 2,
	      Simp_tac 2,
	      constrains_tac 1,
	      rewrite_goals_tac [racts_def, asgt_def],
	      Auto_tac]);


goalw thy [stable_def, invariant_def]
    "stable racts invariant";
by (constrains_tac 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 1);
qed "stable_invariant";

goalw thy [rinit_def, invariant_def] "rinit <= invariant";
by Auto_tac;
qed "rinit_invariant";

goal thy "reachable rinit racts <= invariant";
by (simp_tac (simpset() addsimps
	      [strongest_invariant, stable_invariant, rinit_invariant]) 1); 
qed "reachable_subset_invariant";

val reachable_subset_invariant' = 
    rewrite_rule [invariant_def] reachable_subset_invariant;


(*** Fixedpoint ***)

(*If it reaches a fixedpoint, it has found a solution*)
goalw thy [fixedpoint_def, invariant_def]
    "fixedpoint Int invariant = { %v. (init, v) : edges^* }";
by (rtac equalityI 1);
by (blast_tac (claset() addIs [r_into_rtrancl,rtrancl_trans]) 2);
by (auto_tac (claset() addSIs [ext], simpset()));
by (etac rtrancl_induct 1);
by Auto_tac;
qed "fixedpoint_invariant_correct";

goalw thy (cmd_defs @ [FP_def, fixedpoint_def, stable_def, constrains_def])
    "FP racts <= fixedpoint";
by Auto_tac;
by (dtac bspec 1); 
by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Image_singleton, image_iff]) 1);
by (dtac fun_cong 1);
by Auto_tac;
val lemma1 = result();

goalw thy (cmd_defs @ [FP_def, fixedpoint_def, stable_def, constrains_def])
    "fixedpoint <= FP racts";
by (auto_tac (claset() addIs [ext], simpset()));
val lemma2 = result();

goal thy "FP racts = fixedpoint";
by (rtac ([lemma1,lemma2] MRS equalityI) 1);
qed "FP_fixedpoint";


(*If we haven't reached a fixedpoint then there is some edge for which u but
  not v holds.  Progress will be proved via an ENSURES assertion that the
  metric will decrease for each suitable edge.  A union over all edges proves
  a LEADSTO assertion that the metric decreases if we are not at a fixedpoint.
  *)

goal thy "Compl fixedpoint = (UN (u,v): edges. {s. s u & ~ s v})";
by (simp_tac (simpset() addsimps
	      ([Compl_FP, UN_UN_flatten, FP_fixedpoint RS sym, 
		racts_def, asgt_def])) 1);
by Safe_tac;
by (rtac update_idem 1);
by (Blast_tac 1);
by (Full_simp_tac 1);
by (REPEAT (dtac bspec 1 THEN Simp_tac 1));
by (dtac subsetD 1);
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [update_idem_iff]) 1);
qed "Compl_fixedpoint";

goal thy "A - fixedpoint = (UN (u,v): edges. A Int {s. s u & ~ s v})";
by (simp_tac (simpset() addsimps [Diff_eq, Compl_fixedpoint]) 1);
by (Blast_tac 1);
qed "Diff_fixedpoint";


(*** Progress ***)

goalw thy [metric_def] "!!s. ~ s x ==> Suc (metric (s[x|->True])) = metric s";
by (subgoal_tac "{v. ~ (s[x|->True]) v} = {v. ~ s v} - {x}" 1);
by Auto_tac;
by (asm_simp_tac (simpset() addsimps [card_Suc_Diff]) 1);
qed "Suc_metric";

goal thy "!!s. ~ s x ==> metric (s[x|->True]) < metric s";
by (etac (Suc_metric RS subst) 1);
by (Blast_tac 1);
qed "metric_less";
AddSIs [metric_less];

goal thy "metric (s[y|->s x | s y]) <= metric s";
by (case_tac "s x --> s y" 1);
by (auto_tac (claset() addIs [less_imp_le],
	      simpset() addsimps [update_idem]));
qed "metric_le";

goal thy "!!m. (u,v): edges ==> \
\              ensures racts ((metric-``{m}) Int {s. s u & ~ s v})  \
\                            (metric-``(lessThan m))";
by (ensures_tac "asgt u v" 1);
by (cut_facts_tac [metric_le] 1);
by (fast_tac (claset() addSDs [le_imp_less_or_eq]) 1);
qed "edges_ensures";

goal thy "leadsTo racts ((metric-``{m}) - fixedpoint) (metric-``(lessThan m))";
by (simp_tac (simpset() addsimps [Diff_fixedpoint]) 1);
by (rtac leadsTo_UN 1);
by (split_all_tac 1);
by (asm_simp_tac (simpset() addsimps [edges_ensures RS leadsTo_Basis]) 1);
qed "leadsTo_Diff_fixedpoint";

goal thy "leadsTo racts (metric-``{m}) (metric-``(lessThan m) Un fixedpoint)";
by (rtac (leadsTo_Diff_fixedpoint RS leadsTo_weaken_R RS leadsTo_Diff) 1);
by (ALLGOALS (blast_tac (claset() addIs [subset_imp_leadsTo])));
qed "leadsTo_Un_fixedpoint";


(*Execution in any state leads to a fixedpoint (i.e. can terminate)*)
goal thy "leadsTo racts UNIV fixedpoint";
by (rtac lessThan_induct 1);
by Auto_tac;
by (rtac leadsTo_Un_fixedpoint 1);
qed "leadsTo_fixedpoint";

goal thy "LeadsTo rinit racts UNIV { %v. (init, v) : edges^* }";
by (stac (fixedpoint_invariant_correct RS sym) 1);
by (rtac (leadsTo_fixedpoint RS leadsTo_imp_LeadsTo RS LeadsTo_weaken_R) 1); 
by (cut_facts_tac [reachable_subset_invariant] 1);
by (Blast_tac 1);
qed "LeadsTo_correct";

