(*  Title: 	ZF/ex/Ntree.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition n-ary branching trees
Demonstrates a simple use of function space in a datatype definition

Based upon ex/Term.ML
*)

open Ntree;

(** ntree **)

goal Ntree.thy "ntree(A) = A * (UN n: nat. n -> ntree(A))";
let open ntree;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
val ntree_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t: ntree(A); 							\
\       !!x n h. [| x: A;  n: nat;  h: n -> ntree(A);  ALL i:n. P(h`i)  \
\                |] ==> P(Branch(x,h))  				\
\    |] ==> P(t)";
by (rtac (major RS ntree.induct) 1);
by (etac UN_E 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (ZF_cs addEs [fun_weaken_type]) 1);
by (fast_tac (ZF_cs addDs [apply_type]) 1);
val ntree_induct = result();

(*Induction on ntree(A) to prove an equation*)
val major::prems = goal Ntree.thy
  "[| t: ntree(A);  f: ntree(A)->B;  g: ntree(A)->B;			  \
\     !!x n h. [| x: A;  n: nat;  h: n -> ntree(A);  f O h = g O h |] ==> \
\              f ` Branch(x,h) = g ` Branch(x,h)  			  \
\  |] ==> f`t=g`t";
by (rtac (major RS ntree_induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (cut_facts_tac prems 1);
br fun_extension 1;
by (REPEAT_SOME (ares_tac [comp_fun]));
by (asm_simp_tac (ZF_ss addsimps [comp_fun_apply]) 1);
val ntree_induct_eqn = result();

(**  Lemmas to justify using "Ntree" in other recursive type definitions **)

goalw Ntree.thy ntree.defs "!!A B. A<=B ==> ntree(A) <= ntree(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac ntree.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val ntree_mono = result();

(*Easily provable by induction also*)
goalw Ntree.thy (ntree.defs@ntree.con_defs) "ntree(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (safe_tac ZF_cs);
by (REPEAT (ares_tac [Pair_in_univ, nat_fun_univ RS subsetD] 1));
val ntree_univ = result();

val ntree_subset_univ = [ntree_mono, ntree_univ] MRS subset_trans |> standard;


(** maptree **)

goal Ntree.thy "maptree(A) = A * (maptree(A) -||> maptree(A))";
let open maptree;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
val maptree_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t: maptree(A); 							\
\       !!x n h. [| x: A;  h: maptree(A) -||> maptree(A);  		\
\                   ALL y: field(h). P(y)  				\
\                |] ==> P(Sons(x,h))  					\
\    |] ==> P(t)";
by (rtac (major RS maptree.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (eresolve_tac [Collect_subset RS FiniteFun_mono1 RS subsetD] 1);
by (dresolve_tac [FiniteFun.dom_subset RS subsetD] 1);
by (dresolve_tac [Fin.dom_subset RS subsetD] 1);
by (fast_tac ZF_cs 1);
val maptree_induct = result();


(** maptree2 **)

goal Ntree.thy "maptree2(A,B) = A * (B -||> maptree2(A,B))";
let open maptree2;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
val maptree2_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Ntree.thy
    "[| t: maptree2(A,B); 						  \
\       !!x n h. [| x: A;  h: B -||> maptree2(A,B);  ALL y:range(h). P(y) \
\                |] ==> P(Sons2(x,h))  					  \
\    |] ==> P(t)";
by (rtac (major RS maptree2.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (eresolve_tac [[subset_refl, Collect_subset] MRS
		  FiniteFun_mono RS subsetD] 1);
by (dresolve_tac [FiniteFun.dom_subset RS subsetD] 1);
by (dresolve_tac [Fin.dom_subset RS subsetD] 1);
by (fast_tac ZF_cs 1);
val maptree2_induct = result();

