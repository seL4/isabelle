(*  Title:      HOL/UNITY/Reachability
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Reachability in Graphs

From Chandy and Misra, "Parallel Program Design" (1989), sections 6.2 and 11.3
*)

bind_thm("E_imp_in_V_L", Graph2 RS conjunct1);
bind_thm("E_imp_in_V_R", Graph2 RS conjunct2);

Goal "(v,w) : E ==> F : reachable v LeadsTo nmsg_eq 0 (v,w) Int reachable v";
by (rtac (MA7 RS PSP_Stable RS LeadsTo_weaken_L) 1);
by (rtac MA6 3);
by (auto_tac (claset(), simpset() addsimps [E_imp_in_V_L, E_imp_in_V_R]));
qed "lemma2";

Goal "(v,w) : E ==> F : reachable v LeadsTo reachable w";
by (rtac (MA4 RS Always_LeadsTo_weaken) 1);
by (rtac lemma2 2);
by (auto_tac (claset(), simpset() addsimps [nmsg_eq_def, nmsg_gt_def]));
qed "Induction_base";

Goal "(v,w) : REACHABLE ==> F : reachable v LeadsTo reachable w";
by (etac REACHABLE.induct 1);
by (rtac subset_imp_LeadsTo 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [LeadsTo_Trans, Induction_base]) 1);
qed "REACHABLE_LeadsTo_reachable";

Goal "F : {s. (root,v) : REACHABLE} LeadsTo reachable v";
by (rtac single_LeadsTo_I 1);
by (full_simp_tac (simpset() addsplits [split_if_asm]) 1);
by (rtac (MA1 RS Always_LeadsToI) 1);
by (etac (REACHABLE_LeadsTo_reachable RS LeadsTo_weaken_L) 1);
by Auto_tac;
qed "Detects_part1";


Goalw [Detects_def]
     "v : V ==> F : (reachable v) Detects {s. (root,v) : REACHABLE}";
by Auto_tac;
by (blast_tac (claset() addIs [MA2 RS Always_weaken]) 2);
by (rtac (Detects_part1 RS LeadsTo_weaken_L) 1);
by (Blast_tac 1);
qed "Reachability_Detected";


Goal "v : V ==> F : UNIV LeadsTo (reachable v <==> {s. (root,v) : REACHABLE})";
by (etac (Reachability_Detected RS Detects_Imp_LeadstoEQ) 1);
qed "LeadsTo_Reachability";

(* ------------------------------------ *)

(* Some lemmas about <==> *)

Goalw [Equality_def]
     "(reachable v <==> {s. (root,v) : REACHABLE}) = \
\     {s. ((s : reachable v) = ((root,v) : REACHABLE))}";
by (Blast_tac 1);
qed "Eq_lemma1";


Goalw [Equality_def]
     "(reachable v <==> (if (root,v) : REACHABLE then UNIV else {})) = \
\     {s. ((s : reachable v) = ((root,v) : REACHABLE))}";
by Auto_tac;
qed "Eq_lemma2";

(* ------------------------------------ *)


(* Some lemmas about final (I don't need all of them!)  *)

Goalw [final_def, Equality_def]
     "(INT v: V. INT w:V. {s. ((s : reachable v) = ((root,v) : REACHABLE)) & \
\                             s : nmsg_eq 0 (v,w)}) \
\     <= final";
by Auto_tac;
by (ftac E_imp_in_V_R 1);
by (ftac E_imp_in_V_L 1);
by (Blast_tac 1);
qed "final_lemma1";

Goalw [final_def, Equality_def] 
 "E~={} \
\ ==> (INT v: V. INT e: E. {s. ((s : reachable v) = ((root,v) : REACHABLE))} \
\                          Int nmsg_eq 0 e)    <=  final";
by (auto_tac (claset(), simpset() addsplits [split_if_asm]));
by (ftac E_imp_in_V_L 1);
by (Blast_tac 1);
qed "final_lemma2";

Goal "E~={} \
\     ==> (INT v: V. INT e: E. \
\          (reachable v <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 e) \
\         <= final";
by (ftac final_lemma2 1);
by (simp_tac (simpset() addsimps [Eq_lemma2]) 1);
qed "final_lemma3";


Goal "E~={} \
\     ==> (INT v: V. INT e: E. \
\          {s. ((s : reachable v) = ((root,v) : REACHABLE))} Int nmsg_eq 0 e) \
\         = final";
by (rtac subset_antisym 1);
by (etac final_lemma2 1);
by (rewrite_goals_tac [final_def,Equality_def]);
by (Blast_tac 1); 
qed "final_lemma4";

Goal "E~={} \
\     ==> (INT v: V. INT e: E. \
\          ((reachable v) <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 e) \
\         = final";
by (ftac final_lemma4 1);
by (simp_tac (simpset() addsimps [Eq_lemma2]) 1);
qed "final_lemma5";


Goal "(INT v: V. INT w: V. \
\      (reachable v <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 (v,w)) \
\     <= final";
by (simp_tac (simpset() addsimps [Eq_lemma2, Int_def]) 1);
by (rtac final_lemma1 1);
qed "final_lemma6";


Goalw [final_def] 
     "final = \
\     (INT v: V. INT w: V. \
\      ((reachable v) <==> {s. (root,v) : REACHABLE}) Int \
\      (-{s. (v,w) : E} Un (nmsg_eq 0 (v,w))))";
by (rtac subset_antisym 1);
by (Blast_tac 1);
by (auto_tac (claset(), simpset() addsplits [split_if_asm]));
by (ftac E_imp_in_V_R 1);
by (ftac E_imp_in_V_L 1);
by (Blast_tac 1);
qed "final_lemma7"; 

(* ------------------------------------ *)


(* ------------------------------------ *)

(* Stability theorems *)


Goal "[| v : V; (root,v) ~: REACHABLE |] ==> F : Stable (- reachable v)";
by (dtac (MA2 RS AlwaysD) 1);
by Auto_tac;
qed "not_REACHABLE_imp_Stable_not_reachable";

Goal "v : V ==> F : Stable (reachable v <==> {s. (root,v) : REACHABLE})";
by (simp_tac (simpset() addsimps [Equality_def, Eq_lemma2]) 1);
by (blast_tac (claset() addIs [MA6,not_REACHABLE_imp_Stable_not_reachable]) 1);
qed "Stable_reachable_EQ_R";


Goalw [nmsg_gte_def, nmsg_lte_def,nmsg_gt_def, nmsg_eq_def]
     "((nmsg_gte 0 (v,w) Int nmsg_lte 1 (v,w)) Int (- nmsg_gt 0 (v,w) Un A)) \
\     <= A Un nmsg_eq 0 (v,w)";
by Auto_tac;
qed "lemma4";


Goalw [nmsg_gte_def,nmsg_lte_def,nmsg_gt_def, nmsg_eq_def]
     "reachable v Int nmsg_eq 0 (v,w) = \
\     ((nmsg_gte 0 (v,w) Int nmsg_lte 1 (v,w)) Int \
\      (reachable v Int nmsg_lte 0 (v,w)))";
by Auto_tac;
qed "lemma5";

Goalw [nmsg_gte_def,nmsg_lte_def,nmsg_gt_def, nmsg_eq_def]
     "- nmsg_gt 0 (v,w) Un reachable v <= nmsg_eq 0 (v,w) Un reachable v";
by Auto_tac;
qed "lemma6";

Goal "[|v : V; w : V|] ==> F : Always (reachable v Un nmsg_eq 0 (v,w))";
by (rtac ([MA5, MA3] MRS Always_Int_I RS Always_weaken) 1);
by (rtac lemma4 5); 
by Auto_tac;
qed "Always_reachable_OR_nmsg_0";

Goal "[|v : V; w : V|] ==> F : Stable (reachable v Int nmsg_eq 0 (v,w))";
by (stac lemma5 1);
by (blast_tac (claset() addIs [MA5, Always_imp_Stable RS Stable_Int, MA6b]) 1);
qed "Stable_reachable_AND_nmsg_0";

Goal "[|v : V; w : V|] ==> F : Stable (nmsg_eq 0 (v,w) Un reachable v)";
by (blast_tac (claset() addSIs [Always_weaken RS Always_imp_Stable,
			       lemma6, MA3]) 1);
qed "Stable_nmsg_0_OR_reachable";

Goal "[| v : V; w:V; (root,v) ~: REACHABLE |] \
\     ==> F : Stable (- reachable v Int nmsg_eq 0 (v,w))";
by (rtac ([MA2 RS Always_imp_Stable, Stable_nmsg_0_OR_reachable] MRS 
	  Stable_Int RS Stable_eq) 1);
by (Blast_tac 4);
by Auto_tac;
qed "not_REACHABLE_imp_Stable_not_reachable_AND_nmsg_0";

Goal "[| v : V; w:V |] \
\     ==> F : Stable ((reachable v <==> {s. (root,v) : REACHABLE}) Int \
\                     nmsg_eq 0 (v,w))";
by (asm_simp_tac
    (simpset() addsimps [Equality_def, Eq_lemma2,
			 not_REACHABLE_imp_Stable_not_reachable_AND_nmsg_0,
			 Stable_reachable_AND_nmsg_0]) 1);
qed "Stable_reachable_EQ_R_AND_nmsg_0";


(* ------------------------------------ *)


(* LeadsTo final predicate (Exercise 11.2 page 274) *)

Goal "UNIV <= (INT v: V. UNIV)";
by (Blast_tac 1);
val UNIV_lemma = result();

val UNIV_LeadsTo_completion = 
    [Finite_stable_completion, UNIV_lemma] MRS LeadsTo_weaken_L;

Goalw [final_def] "E={} ==> F : UNIV LeadsTo final";
by (Asm_full_simp_tac 1);
by (rtac UNIV_LeadsTo_completion 1);
by Safe_tac;
by (etac (simplify (simpset()) LeadsTo_Reachability) 1);
by (dtac Stable_reachable_EQ_R 1);
by (Asm_full_simp_tac 1);
qed "LeadsTo_final_E_empty";


Goal "[| v : V; w:V |] \
\  ==> F : UNIV LeadsTo \
\          ((reachable v <==> {s. (root,v): REACHABLE}) Int nmsg_eq 0 (v,w))";
by (rtac (LeadsTo_Reachability RS LeadsTo_Trans) 1);
by (Blast_tac 1);
by (subgoal_tac "F : (reachable v <==> {s. (root,v) : REACHABLE}) Int UNIV LeadsTo (reachable v <==> {s. (root,v) : REACHABLE}) Int nmsg_eq 0 (v,w)" 1);
by (Asm_full_simp_tac 1);
by (rtac PSP_Stable2 1);
by (rtac MA7 1); 
by (rtac Stable_reachable_EQ_R 3);
by Auto_tac;
qed "Leadsto_reachability_AND_nmsg_0";


Goal "E~={} ==> F : UNIV LeadsTo final";
by (rtac ([LeadsTo_weaken_R, UNIV_lemma] MRS LeadsTo_weaken_L) 1);
by (rtac final_lemma6 2);
by (rtac Finite_stable_completion 1);
by (Blast_tac 1); 
by (rtac UNIV_LeadsTo_completion 1);
by (REPEAT
    (blast_tac (claset() addIs [Stable_INT,
				Stable_reachable_EQ_R_AND_nmsg_0,
				Leadsto_reachability_AND_nmsg_0]) 1));
qed "LeadsTo_final_E_NOT_empty";


Goal "F : UNIV LeadsTo final";
by (case_tac "E={}" 1);
by (rtac LeadsTo_final_E_NOT_empty 2);
by (rtac LeadsTo_final_E_empty 1);
by Auto_tac;
qed "LeadsTo_final";

(* ------------------------------------ *)

(* Stability of final (Exercise 11.2 page 274) *)

Goalw [final_def] "E={} ==> F : Stable final";
by (Asm_full_simp_tac 1);
by (rtac Stable_INT 1); 
by (dtac Stable_reachable_EQ_R 1);
by (Asm_full_simp_tac 1);
qed "Stable_final_E_empty";


Goal "E~={} ==> F : Stable final";
by (stac final_lemma7 1); 
by (rtac Stable_INT 1); 
by (rtac Stable_INT 1); 
by (simp_tac (simpset() addsimps [Eq_lemma2]) 1);
by Safe_tac;
by (rtac Stable_eq 1);
by (subgoal_tac "({s. (s : reachable v) = ((root,v) : REACHABLE)} Int nmsg_eq 0 (v,w)) = \
\                ({s. (s : reachable v) = ((root,v) : REACHABLE)} Int (- UNIV Un nmsg_eq 0 (v,w)))" 2);
by (Blast_tac 2); by (Blast_tac 2);
by (rtac (simplify (simpset() addsimps [Eq_lemma2]) Stable_reachable_EQ_R_AND_nmsg_0) 1);
by (Blast_tac 1);by (Blast_tac 1);
by (rtac Stable_eq 1);
by (subgoal_tac "({s. (s : reachable v) = ((root,v) : REACHABLE)}) = ({s. (s : reachable v) = ((root,v) : REACHABLE)} Int (- {} Un nmsg_eq 0 (v,w)))" 2);
by (Blast_tac 2); by (Blast_tac 2);
by (rtac (simplify (simpset() addsimps [Eq_lemma2]) Stable_reachable_EQ_R) 1);
by Auto_tac;
qed "Stable_final_E_NOT_empty";

Goal "F : Stable final";
by (case_tac "E={}" 1);
by (blast_tac (claset() addIs [Stable_final_E_NOT_empty]) 2);
by (blast_tac (claset() addIs [Stable_final_E_empty]) 1);
qed "Stable_final";
