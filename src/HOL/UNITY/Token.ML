(*  Title:      HOL/UNITY/Token
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Token Ring.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.
*)

val Token_defs = [HasTok_def, H_def, E_def, T_def];

Goalw [HasTok_def] "[| s: HasTok i; s: HasTok j |] ==> i=j";
by Auto_tac;
qed "HasToK_partition";

Goalw Token_defs "(s ~: E i) = (s : H i | s : T i)";
by (Simp_tac 1);
by (exhaust_tac "proc s i" 1);
by Auto_tac;
qed "not_E_eq";

Open_locale "Token";

val TR2 = thm "TR2";
val TR3 = thm "TR3";
val TR4 = thm "TR4";
val TR5 = thm "TR5";
val TR6 = thm "TR6";
val TR7 = thm "TR7";
val nodeOrder_def = thm "nodeOrder_def";
val next_def = thm "next_def";

AddIffs [thm "N_positive"];

Goalw [stable_def] "F : stable (-(E i) Un (HasTok i))";
by (rtac constrains_weaken 1);
by (rtac ([[TR2, TR4] MRS constrains_Un, TR5] MRS constrains_Un) 1);
by (auto_tac (claset(), simpset() addsimps [not_E_eq]));
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [H_def, E_def, T_def])));
qed "token_stable";


(*** Progress under weak fairness ***)

Goalw [nodeOrder_def] "wf(nodeOrder j)";
by (rtac (wf_less_than RS wf_inv_image RS wf_subset) 1);
by (Blast_tac 1);
qed"wf_nodeOrder";

Goalw [nodeOrder_def, next_def, inv_image_def]
    "[| i<N; j<N |] ==> ((next i, i) : nodeOrder j) = (i ~= j)";
by (auto_tac (claset(),
	      simpset() addsimps [Suc_lessI, mod_Suc, mod_less, mod_geq]));
by (subgoal_tac "(j + N - i) = Suc (j + N - Suc i)" 1);
by (asm_simp_tac (simpset() addsimps [Suc_diff_Suc, Suc_leI, less_imp_le,
                                      diff_add_assoc]) 2);
by (full_simp_tac (simpset() addsimps [linorder_neq_iff]) 1);
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq, mod_Suc]) 1);
by (auto_tac (claset(), 
              simpset() addsimps [diff_add_assoc2, linorder_neq_iff, 
                                  Suc_le_eq, Suc_diff_Suc, less_imp_diff_less, 
                                  add_diff_less, mod_less, mod_geq]));
qed "nodeOrder_eq";


(*From "A Logic for Concurrent Programming", but not used in Chapter 4.
  Note the use of case_tac.  Reasoning about leadsTo takes practice!*)
Goal "[| i<N; j<N |] ==>   \
\     F : (HasTok i) leadsTo ({s. (token s, i) : nodeOrder j} Un HasTok j)";
by (case_tac "i=j" 1);
by (blast_tac (claset() addIs [subset_imp_leadsTo]) 1);
by (rtac (TR7 RS leadsTo_weaken_R) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [HasTok_def, nodeOrder_eq]) 1);
qed "TR7_nodeOrder";


(*Chapter 4 variant, the one actually used below.*)
Goal "[| i<N; j<N; i~=j |]    \
\     ==> F : (HasTok i) leadsTo {s. (token s, i) : nodeOrder j}";
by (rtac (TR7 RS leadsTo_weaken_R) 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [HasTok_def, nodeOrder_eq]) 1);
qed "TR7_aux";

Goal "({s. token s < N} Int token -`` {m}) = \
\     (if m<N then token -`` {m} else {})";
by Auto_tac;
val token_lemma = result();


(*Misra's TR9: the token reaches an arbitrary node*)
Goal "j<N ==> F : {s. token s < N} leadsTo (HasTok j)";
by (rtac leadsTo_weaken_R 1);
by (res_inst_tac [("I", "-{j}"), ("f", "token"), ("B", "{}")]
     (wf_nodeOrder RS bounded_induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [token_lemma, vimage_Diff,
						HasTok_def])));
by (Blast_tac 2);
by (Clarify_tac 1);
by (rtac (TR7_aux RS leadsTo_weaken) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [nodeOrder_def, HasTok_def])));
by (ALLGOALS Blast_tac);
qed "leadsTo_j";

(*Misra's TR8: a hungry process eventually eats*)
Goal "j<N ==> F : ({s. token s < N} Int H j) leadsTo (E j)";
by (rtac (leadsTo_cancel1 RS leadsTo_Un_duplicate) 1);
by (rtac TR6 2);
by (rtac leadsTo_weaken_R 1);
by (rtac ([leadsTo_j, TR3] MRS psp) 1);
by (ALLGOALS Blast_tac);
qed "token_progress";
