(*  Title:      ZF/ex/BT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of binary trees
*)

(*Perform induction on l, then prove the major premise using prems. *)
fun bt_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] bt.induct i,
           rename_last_tac a ["1","2"] (i+2),
           ares_tac prems i];


Addsimps bt.intrs;

(**  Lemmas to justify using "bt" in other recursive type definitions **)

Goalw bt.defs "A<=B ==> bt(A) <= bt(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac bt.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "bt_mono";

Goalw (bt.defs@bt.con_defs) "bt(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (fast_tac (claset() addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
                            Pair_in_univ]) 1);
qed "bt_univ";

bind_thm ("bt_subset_univ", [bt_mono, bt_univ] MRS subset_trans);


(*Type checking -- proved by induction, as usual*)
val prems = goal BT.thy
    "[| t: bt(A);    \
\       c: C(Lf);       \
\       !!x y z r s. [| x:A;  y:bt(A);  z:bt(A);  r:C(y);  s:C(z) |] ==> \
\                    h(x,y,z,r,s): C(Br(x,y,z))  \
\    |] ==> bt_rec(c,h,t) : C(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "bt_rec_type";

(** n_nodes **)

Goal "t: bt(A) ==> n_nodes(t) : nat";
by (bt_ind_tac "t" [] 1);
by Auto_tac;
qed "n_nodes_type";


(** n_leaves **)

Goal "t: bt(A) ==> n_leaves(t) : nat";
by (bt_ind_tac "t" [] 1);
by Auto_tac;
qed "n_leaves_type";

(** bt_reflect **)

Goal "t: bt(A) ==> bt_reflect(t) : bt(A)";
by (bt_ind_tac "t" [] 1);
by Auto_tac;
by (REPEAT (ares_tac (bt.intrs @ [bt_rec_type]) 1));
qed "bt_reflect_type";


(** BT simplification **)


Addsimps [bt_rec_type, n_nodes_type, n_leaves_type, bt_reflect_type];


(*** theorems about n_leaves ***)

val prems = goal BT.thy
    "t: bt(A) ==> n_leaves(bt_reflect(t)) = n_leaves(t)";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_commute, n_leaves_type])));
qed "n_leaves_reflect";

val prems = goal BT.thy
    "t: bt(A) ==> n_leaves(t) = succ(n_nodes(t))";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_succ_right])));
qed "n_leaves_nodes";

(*** theorems about bt_reflect ***)

val prems = goal BT.thy
    "t: bt(A) ==> bt_reflect(bt_reflect(t))=t";
by (bt_ind_tac "t" prems 1);
by (ALLGOALS Asm_simp_tac);
qed "bt_reflect_bt_reflect_ident";


