(*  Title: 	ZF/ex/BT.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of binary trees
*)

open BT;

(*Perform induction on l, then prove the major premise using prems. *)
fun bt_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] bt.induct i,
	   rename_last_tac a ["1","2"] (i+2),
	   ares_tac prems i];


(**  Lemmas to justify using "bt" in other recursive type definitions **)

goalw BT.thy bt.defs "!!A B. A<=B ==> bt(A) <= bt(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac bt.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "bt_mono";

goalw BT.thy (bt.defs@bt.con_defs) "bt(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (fast_tac (ZF_cs addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
			    Pair_in_univ]) 1);
qed "bt_univ";

bind_thm ("bt_subset_univ", ([bt_mono, bt_univ] MRS subset_trans));


(** bt_rec -- by Vset recursion **)

goalw BT.thy bt.con_defs "rank(l) < rank(Br(a,l,r))";
by (simp_tac rank_ss 1);
qed "rank_Br1";

goalw BT.thy bt.con_defs "rank(r) < rank(Br(a,l,r))";
by (simp_tac rank_ss 1);
qed "rank_Br2";

goal BT.thy "bt_rec(Lf,c,h) = c";
by (rtac (bt_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (ZF_ss addsimps bt.case_eqns) 1);
qed "bt_rec_Lf";

goal BT.thy
    "bt_rec(Br(a,l,r), c, h) = h(a, l, r, bt_rec(l,c,h), bt_rec(r,c,h))";
by (rtac (bt_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (rank_ss addsimps (bt.case_eqns @ [rank_Br1, rank_Br2])) 1);
qed "bt_rec_Br";

(*Type checking -- proved by induction, as usual*)
val prems = goal BT.thy
    "[| t: bt(A);    \
\       c: C(Lf);       \
\       !!x y z r s. [| x:A;  y:bt(A);  z:bt(A);  r:C(y);  s:C(z) |] ==> \
\		     h(x,y,z,r,s): C(Br(x,y,z))  \
\    |] ==> bt_rec(t,c,h) : C(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps
			    (prems@[bt_rec_Lf,bt_rec_Br]))));
qed "bt_rec_type";

(** Versions for use with definitions **)

val [rew] = goal BT.thy "[| !!t. j(t)==bt_rec(t, c, h) |] ==> j(Lf) = c";
by (rewtac rew);
by (rtac bt_rec_Lf 1);
qed "def_bt_rec_Lf";

val [rew] = goal BT.thy
    "[| !!t. j(t)==bt_rec(t, c, h) |] ==> j(Br(a,l,r)) = h(a,l,r,j(l),j(r))";
by (rewtac rew);
by (rtac bt_rec_Br 1);
qed "def_bt_rec_Br";

fun bt_recs def = map standard ([def] RL [def_bt_rec_Lf, def_bt_rec_Br]);

(** n_nodes **)

val [n_nodes_Lf,n_nodes_Br] = bt_recs n_nodes_def;

val prems = goalw BT.thy [n_nodes_def] 
    "xs: bt(A) ==> n_nodes(xs) : nat";
by (REPEAT (ares_tac (prems @ [bt_rec_type, nat_0I, nat_succI, add_type]) 1));
qed "n_nodes_type";


(** n_leaves **)

val [n_leaves_Lf,n_leaves_Br] = bt_recs n_leaves_def;

val prems = goalw BT.thy [n_leaves_def] 
    "xs: bt(A) ==> n_leaves(xs) : nat";
by (REPEAT (ares_tac (prems @ [bt_rec_type, nat_0I, nat_succI, add_type]) 1));
qed "n_leaves_type";

(** bt_reflect **)

val [bt_reflect_Lf, bt_reflect_Br] = bt_recs bt_reflect_def;

goalw BT.thy [bt_reflect_def] "!!xs. xs: bt(A) ==> bt_reflect(xs) : bt(A)";
by (REPEAT (ares_tac (bt.intrs @ [bt_rec_type]) 1));
qed "bt_reflect_type";


(** BT simplification **)


val bt_typechecks =
    bt.intrs @ [bt_rec_type, n_nodes_type, n_leaves_type, bt_reflect_type];

val bt_ss = arith_ss 
    addsimps bt.case_eqns
    addsimps bt_typechecks
    addsimps [bt_rec_Lf, bt_rec_Br, 
	     n_nodes_Lf, n_nodes_Br,
	     n_leaves_Lf, n_leaves_Br,
	     bt_reflect_Lf, bt_reflect_Br];


(*** theorems about n_leaves ***)

val prems = goal BT.thy
    "t: bt(A) ==> n_leaves(bt_reflect(t)) = n_leaves(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac bt_ss));
by (REPEAT (ares_tac [add_commute, n_leaves_type] 1));
qed "n_leaves_reflect";

val prems = goal BT.thy
    "t: bt(A) ==> n_leaves(t) = succ(n_nodes(t))";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [add_succ_right])));
qed "n_leaves_nodes";

(*** theorems about bt_reflect ***)

val prems = goal BT.thy
    "t: bt(A) ==> bt_reflect(bt_reflect(t))=t";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac bt_ss));
qed "bt_reflect_bt_reflect_ident";


