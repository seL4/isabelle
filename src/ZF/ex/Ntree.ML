(*  Title:      ZF/ex/Ntree.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition

Based upon ex/Term.ML
*)

(** ntree **)

Goal "ntree(A) = A * (\\<Union>n \\<in> nat. n -> ntree(A))";
let open ntree;  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (map rew intrs) addEs [rew elim]) 1)
end;
qed "ntree_unfold";

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t \\<in> ntree(A);                                                    \
\       !!x n h. [| x \\<in> A;  n \\<in> nat;  h \\<in> n -> ntree(A);  \\<forall>i \\<in> n. P(h`i)  \
\                |] ==> P(Branch(x,h))                                  \
\    |] ==> P(t)";
by (rtac (major RS ntree.induct) 1);
by (etac UN_E 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (claset() addEs [fun_weaken_type]) 1);
by (fast_tac (claset() addDs [apply_type]) 1);
qed "ntree_induct";

(*Induction on ntree(A) to prove an equation*)
val major::prems = goal Ntree.thy
  "[| t \\<in> ntree(A);  f \\<in> ntree(A)->B;  g \\<in> ntree(A)->B;                      \
\     !!x n h. [| x \\<in> A;  n \\<in> nat;  h \\<in> n -> ntree(A);  f O h = g O h |] ==> \
\              f ` Branch(x,h) = g ` Branch(x,h)                          \
\  |] ==> f`t=g`t";
by (rtac (major RS ntree_induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (cut_facts_tac prems 1);
by (rtac fun_extension 1);
by (REPEAT_SOME (ares_tac [comp_fun]));
by (asm_simp_tac (simpset() addsimps [comp_fun_apply]) 1);
qed "ntree_induct_eqn";

(**  Lemmas to justify using "Ntree" in other recursive type definitions **)

Goalw ntree.defs "A \\<subseteq> B ==> ntree(A) \\<subseteq> ntree(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac ntree.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "ntree_mono";

(*Easily provable by induction also*)
Goalw (ntree.defs@ntree.con_defs) "ntree(univ(A)) \\<subseteq> univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by Safe_tac;
by (REPEAT (ares_tac [Pair_in_univ, nat_fun_univ RS subsetD] 1));
qed "ntree_univ";

val ntree_subset_univ = [ntree_mono, ntree_univ] MRS subset_trans |> standard;


(** ntree recursion **)

Goal "ntree_rec(b, Branch(x,h)) \
\     = b(x, h, \\<lambda>i \\<in> domain(h). ntree_rec(b, h`i))";
by (rtac (ntree_rec_def RS def_Vrecursor RS trans) 1);
by (Simp_tac 1);
by (rewrite_goals_tac ntree.con_defs);
by (asm_simp_tac (simpset() addsimps [rank_pair2 RSN (2, lt_trans), 
				      rank_apply]) 1);;
qed "ntree_rec_Branch";

Goalw [ntree_copy_def]
 "ntree_copy (Branch(x, h)) = Branch(x, \\<lambda>i \\<in> domain(h). ntree_copy (h`i))";
by (rtac ntree_rec_Branch 1);
qed "ntree_copy_Branch";

Addsimps [ntree_copy_Branch];

Goal "z \\<in> ntree(A) ==> ntree_copy(z) = z";
by (induct_tac "z" 1);
by (auto_tac (claset(), simpset() addsimps [domain_of_fun, Pi_Collect_iff]));
qed "ntree_copy_is_ident";



(** maptree **)

Goal "maptree(A) = A * (maptree(A) -||> maptree(A))";
let open maptree;  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (map rew intrs) addEs [rew elim]) 1)
end;
qed "maptree_unfold";

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t \\<in> maptree(A);                                                  \
\       !!x n h. [| x \\<in> A;  h \\<in> maptree(A) -||> maptree(A);               \
\                   \\<forall>y \\<in> field(h). P(y)                               \
\                |] ==> P(Sons(x,h))                                    \
\    |] ==> P(t)";
by (rtac (major RS maptree.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (eresolve_tac [Collect_subset RS FiniteFun_mono1 RS subsetD] 1);
by (dresolve_tac [FiniteFun.dom_subset RS subsetD] 1);
by (dresolve_tac [Fin.dom_subset RS subsetD] 1);
by (Fast_tac 1);
qed "maptree_induct";


(** maptree2 **)

Goal "maptree2(A,B) = A * (B -||> maptree2(A,B))";
let open maptree2;  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (map rew intrs) addEs [rew elim]) 1)
end;
qed "maptree2_unfold";

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t \\<in> maptree2(A,B);                                                 \
\       !!x n h. [| x \\<in> A;  h \\<in> B -||> maptree2(A,B);  \\<forall>y \\<in> range(h). P(y) \
\                |] ==> P(Sons2(x,h))                                     \
\    |] ==> P(t)";
by (rtac (major RS maptree2.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (eresolve_tac [[subset_refl, Collect_subset] MRS
                  FiniteFun_mono RS subsetD] 1);
by (dresolve_tac [FiniteFun.dom_subset RS subsetD] 1);
by (dresolve_tac [Fin.dom_subset RS subsetD] 1);
by (Fast_tac 1);
qed "maptree2_induct";

