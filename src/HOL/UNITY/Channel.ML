(*  Title:      HOL/UNITY/Channel
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unordered Channel

From Misra, "A Logic for Concurrent Programming" (1994), section 13.3
*)

(*None represents "infinity" while Some represents proper integers*)
Goalw [minSet_def] "minSet A = Some x --> x : A";
by (Simp_tac 1);
by (fast_tac (claset() addIs [LeastI]) 1);
qed_spec_mp "minSet_eq_SomeD";

Goalw [minSet_def] " minSet{} = None";
by (Asm_simp_tac 1);
qed_spec_mp "minSet_empty";
Addsimps [minSet_empty];

Goalw [minSet_def] "x:A ==> minSet A = Some (LEAST x. x: A)";
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed_spec_mp "minSet_nonempty";

Goal "F : (minSet -`` {Some x}) leadsTo (minSet -`` (Some``greaterThan x))";
by (rtac leadsTo_weaken 1);
by (rtac ([UC2, UC1] MRS psp) 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
by Safe_tac;
by (auto_tac (claset() addDs [minSet_eq_SomeD], 
	      simpset() addsimps [le_def, linorder_neq_iff]));
qed "minSet_greaterThan";


(*The induction*)
Goal "F : (UNIV-{{}}) leadsTo (minSet -`` (Some``atLeast y))";
by (rtac leadsTo_weaken_R 1);
by (res_inst_tac  [("l", "y"), ("f", "the o minSet"), ("B", "{}")]
     greaterThan_bounded_induct 1);
by Safe_tac;
by (ALLGOALS Asm_simp_tac);
by (dtac minSet_nonempty 2);
by (Asm_full_simp_tac 2);
by (rtac (minSet_greaterThan RS leadsTo_weaken) 1);
by Safe_tac;
by (ALLGOALS Asm_full_simp_tac);
by (dtac minSet_nonempty 1);
by (Asm_full_simp_tac 1);
val lemma = result();


Goal "!!y::nat. F : (UNIV-{{}}) leadsTo {s. y ~: s}";
by (rtac (lemma RS leadsTo_weaken_R) 1);
by (Clarify_tac 1);
by (forward_tac [minSet_nonempty] 1);
by (asm_full_simp_tac (simpset() addsimps [Suc_le_eq]) 1);
by (blast_tac (claset() addDs [Suc_le_lessD, not_less_Least]) 1);
qed "Channel_progress";
