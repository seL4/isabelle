(*  Title: 	ZF/bt.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For bt.thy.  Binary trees
*)

open BT_Fn;



(** bt_rec -- by Vset recursion **)

goalw BT.thy BT.con_defs "rank(l) : rank(Br(a,l,r))";
by (simp_tac rank_ss 1);
val rank_Br1 = result();

goalw BT.thy BT.con_defs "rank(r) : rank(Br(a,l,r))";
by (simp_tac rank_ss 1);
val rank_Br2 = result();

goal BT_Fn.thy "bt_rec(Lf,c,h) = c";
by (rtac (bt_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (ZF_ss addsimps BT.case_eqns) 1);
val bt_rec_Lf = result();

goal BT_Fn.thy
    "bt_rec(Br(a,l,r), c, h) = h(a, l, r, bt_rec(l,c,h), bt_rec(r,c,h))";
by (rtac (bt_rec_def RS def_Vrec RS trans) 1);
by (simp_tac (ZF_ss addsimps 
	      (BT.case_eqns @ [Vset_rankI, rank_Br1, rank_Br2])) 1);
val bt_rec_Br = result();

(*Type checking -- proved by induction, as usual*)
val prems = goal BT_Fn.thy
    "[| t: bt(A);    \
\       c: C(Lf);       \
\       !!x y z r s. [| x:A;  y:bt(A);  z:bt(A);  r:C(y);  s:C(z) |] ==> \
\		     h(x,y,z,r,s): C(Br(x,y,z))  \
\    |] ==> bt_rec(t,c,h) : C(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps
			    (prems@[bt_rec_Lf,bt_rec_Br]))));
val bt_rec_type = result();

(** Versions for use with definitions **)

val [rew] = goal BT_Fn.thy "[| !!t. j(t)==bt_rec(t, c, h) |] ==> j(Lf) = c";
by (rewtac rew);
by (rtac bt_rec_Lf 1);
val def_bt_rec_Lf = result();

val [rew] = goal BT_Fn.thy
    "[| !!t. j(t)==bt_rec(t, c, h) |] ==> j(Br(a,l,r)) = h(a,l,r,j(l),j(r))";
by (rewtac rew);
by (rtac bt_rec_Br 1);
val def_bt_rec_Br = result();

fun bt_recs def = map standard ([def] RL [def_bt_rec_Lf, def_bt_rec_Br]);

(** n_nodes **)

val [n_nodes_Lf,n_nodes_Br] = bt_recs n_nodes_def;

val prems = goalw BT_Fn.thy [n_nodes_def] 
    "xs: bt(A) ==> n_nodes(xs) : nat";
by (REPEAT (ares_tac (prems @ [bt_rec_type, nat_0I, nat_succI, add_type]) 1));
val n_nodes_type = result();


(** n_leaves **)

val [n_leaves_Lf,n_leaves_Br] = bt_recs n_leaves_def;

val prems = goalw BT_Fn.thy [n_leaves_def] 
    "xs: bt(A) ==> n_leaves(xs) : nat";
by (REPEAT (ares_tac (prems @ [bt_rec_type, nat_0I, nat_succI, add_type]) 1));
val n_leaves_type = result();

(** bt_reflect **)

val [bt_reflect_Lf, bt_reflect_Br] = bt_recs bt_reflect_def;

val prems = goalw BT_Fn.thy [bt_reflect_def] 
    "xs: bt(A) ==> bt_reflect(xs) : bt(A)";
by (REPEAT (ares_tac (prems @ [bt_rec_type, LfI, BrI]) 1));
val bt_reflect_type = result();


(** BT_Fn simplification **)


val bt_typechecks =
      [LfI, BrI, bt_rec_type, n_nodes_type, n_leaves_type, bt_reflect_type];

val bt_ss = arith_ss 
    addsimps BT.case_eqns
    addsimps bt_typechecks
    addsimps [bt_rec_Lf, bt_rec_Br, 
	     n_nodes_Lf, n_nodes_Br,
	     n_leaves_Lf, n_leaves_Br,
	     bt_reflect_Lf, bt_reflect_Br];


(*** theorems about n_leaves ***)

val prems = goal BT_Fn.thy
    "t: bt(A) ==> n_leaves(bt_reflect(t)) = n_leaves(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac bt_ss));
by (REPEAT (ares_tac [add_commute, n_leaves_type] 1));
val n_leaves_reflect = result();

val prems = goal BT_Fn.thy
    "t: bt(A) ==> n_leaves(t) = succ(n_nodes(t))";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (bt_ss addsimps [add_succ_right])));
val n_leaves_nodes = result();

(*** theorems about bt_reflect ***)

val prems = goal BT_Fn.thy
    "t: bt(A) ==> bt_reflect(bt_reflect(t))=t";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac bt_ss));
val bt_reflect_bt_reflect_ident = result();


