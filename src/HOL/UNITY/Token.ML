(*  Title:      HOL/UNITY/Token
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Token Ring.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.
*)


open Token;


val Token_defs = [WellTyped_def, Token_def, HasTok_def, H_def, E_def, T_def];

AddIffs [N_positive, skip];

goalw thy [HasTok_def] "!!i. [| s: HasTok i; s: HasTok j |] ==> i=j";
by Auto_tac;
qed "HasToK_partition";

goalw thy Token_defs "!!s. s : WellTyped ==> (s ~: E i) = (s : H i | s : T i)";
by (Simp_tac 1);
by (exhaust_tac "s (Suc i)" 1);
by Auto_tac;
qed "not_E_eq";

(** We should be able to prove WellTyped as a separate Invariant.  Then
    the Invariant rule should let us assume that the initial
    state is reachable, and therefore contained in any Invariant.  Then
    we'd not have to mention WellTyped in the statement of this theorem.
**)

goalw thy [stable_def]
    "stable Acts (WellTyped Int {s. s : E i --> s : HasTok i})";
by (rtac (stable_WT RS stable_constrains_Int) 1);
by (cut_facts_tac [TR2,TR4,TR5] 1);
by (asm_full_simp_tac (simpset() addsimps [constrains_def]) 1);
by (REPEAT_FIRST (rtac ballI ORELSE' (dtac bspec THEN' assume_tac)));
by (auto_tac (claset(), simpset() addsimps [not_E_eq]));
by (case_tac "xa : HasTok i" 1);
by (auto_tac (claset(), simpset() addsimps [H_def, E_def, T_def]));
qed "token_stable";

(*This proof is in the "massaging" style and is much faster! *)
goalw thy [stable_def]
    "stable Acts (WellTyped Int (Compl(E i) Un (HasTok i)))";
by (rtac (stable_WT RS stable_constrains_Int) 1);
by (rtac constrains_weaken 1);
by (rtac ([[TR2, TR4] MRS constrains_Un, TR5] MRS constrains_Un) 1);
by (auto_tac (claset(), simpset() addsimps [not_E_eq]));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [H_def, E_def, T_def])));
qed "token_stable";


(*** Progress under weak fairness ***)

goalw thy [nodeOrder_def] "wf(nodeOrder j)";
by (rtac (wf_less_than RS wf_inv_image RS wf_subset) 1);
by (Blast_tac 1);
qed"wf_nodeOrder";

    goal thy "!!m. [| m<n; Suc m ~= n |] ==> Suc(m) < n";
    by (full_simp_tac (simpset() addsimps [nat_neq_iff]) 1);
    by (blast_tac (claset() addEs [less_asym, less_SucE]) 1);
    qed "Suc_lessI";

goalw thy [nodeOrder_def, next_def, inv_image_def]
    "!!x. [| i<N; j<N |] ==> ((next i, i) : nodeOrder j) = (i ~= j)";
by (auto_tac (claset(),
	      simpset() addsimps [Suc_lessI, mod_Suc, mod_less, mod_geq]));
by (dtac sym 1);
(*The next two lines...**)
by (REPEAT (eres_inst_tac [("P", "?a<N")] rev_mp 1));
by (etac ssubst 1);
(*were with the previous version of asm_full_simp_tac...
  by (rotate_tac ~1 1);
*)
by (asm_full_simp_tac (simpset() addsimps [eq_sym_conv, mod_Suc, mod_less]) 1);
by (subgoal_tac "(j + N - i) = Suc (j + N - Suc i)" 1);
by (asm_simp_tac (simpset() addsimps [Suc_diff_Suc, less_imp_le, Suc_leI, 
                                      diff_add_assoc]) 2);
by (full_simp_tac (simpset() addsimps [nat_neq_iff]) 1);
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq, mod_Suc]) 1);
(*including less_asym here would slow things down*)
by (auto_tac (claset() delrules [notI], 
              simpset() addsimps [diff_add_assoc2, Suc_leI,
                                  less_imp_diff_less, 
                                  mod_less, mod_geq, nat_neq_iff]));
by (REPEAT (blast_tac (claset() addEs [less_asym]) 3));
by (asm_simp_tac (simpset() addsimps [less_imp_diff_less,
				      Suc_diff_n RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [add_diff_less, mod_less]) 1);
by (etac subst 1);
by (asm_simp_tac (simpset() addsimps [add_diff_less]) 1);
qed "nodeOrder_eq";


(*From "A Logic for Concurrent Programming", but not used in Chapter 4.
  Note the use of case_tac.  Reasoning about leadsTo takes practice!*)
goal thy
 "!!i. [| i<N; j<N |] ==> \
\      leadsTo Acts (HasTok i) ({s. (Token s, i) : nodeOrder j} Un HasTok j)";
by (case_tac "i=j" 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
by (rtac (TR7 RS leadsTo_weaken_R) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [HasTok_def, nodeOrder_eq]) 1);
qed "TR7_nodeOrder";


(*Chapter 4 variant, the one actually used below.*)
goal thy
 "!!i. [| i<N; j<N; i~=j |] ==> \
\      leadsTo Acts (HasTok i) {s. (Token s, i) : nodeOrder j}";
by (rtac (TR7 RS leadsTo_weaken_R) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [HasTok_def, nodeOrder_eq]) 1);
qed "TR7_aux";

goal thy "({s. Token s < N} Int Token -`` {m}) = \
\         (if m<N then Token -`` {m} else {})";
by Auto_tac;
val Token_lemma = result();


(*Misra's TR9: the token reaches an arbitrary node*)
goal thy
 "!!i. j<N ==> leadsTo Acts {s. Token s < N} (HasTok j)";
by (rtac leadsTo_weaken_R 1);
by (res_inst_tac [("I", "Compl{j}"), ("f", "Token"), ("B", "{}")]
     (wf_nodeOrder RS bounded_induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Token_lemma, vimage_Diff,
						HasTok_def])));
by (Blast_tac 2);
by (Clarify_tac 1);
by (rtac (TR7_aux RS leadsTo_weaken) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [nodeOrder_def, HasTok_def])));
by (ALLGOALS Blast_tac);
qed "leadsTo_j";

(*Misra's TR8: a hungry process eventually eats*)
goal thy "!!i. j<N ==> leadsTo Acts ({s. Token s < N} Int H j) (E j)";
by (rtac (leadsTo_cancel1 RS leadsTo_Un_duplicate) 1);
by (rtac TR6 2);
by (rtac leadsTo_weaken_R 1);
by (rtac ([leadsTo_j, TR3] MRS PSP) 1);
by (ALLGOALS Blast_tac);
qed "Token_progress";
