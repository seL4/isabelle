(*  Title:      HOL/ex/LocaleGroup.ML
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Group theory via records and locales.
*)

Open_locale "groups";
print_locales LocaleGroup.thy;

val simp_G = simplify (simpset() addsimps [Group_def]) (thm "Group_G");
Addsimps [simp_G, thm "Group_G"];


goal LocaleGroup.thy "e : carrier G";
by (afs [thm "e_def"] 1);
val e_closed = result();

(* Mit dieser Def ist es halt schwierig *)
goal LocaleGroup.thy "op # : carrier G -> carrier G -> carrier G";
by (res_inst_tac [("t","op #")] ssubst 1);
by (rtac ext 1);
by (rtac ext 1);
by (rtac meta_eq_to_obj_eq 1);
by (rtac (thm "binop_def") 1);
by (Asm_full_simp_tac 1);
val binop_funcset = result();

goal LocaleGroup.thy "!! x y. [| x: carrier G; y: carrier G |] ==> x # y : carrier G";
by (afs [binop_funcset RS funcset2E1] 1);
val binop_closed = result();

goal LocaleGroup.thy "inv : carrier G -> carrier G";
by (res_inst_tac [("t","inv")] ssubst 1);
by (rtac ext 1);
by (rtac meta_eq_to_obj_eq 1);
by (rtac (thm "inv_def") 1);
by (Asm_full_simp_tac 1);
val inv_funcset = result();

goal LocaleGroup.thy "!! x . x: carrier G ==> x -| : carrier G";
by (afs [inv_funcset RS funcsetE1] 1);
val inv_closed = result(); 


goal LocaleGroup.thy "!! x . x: carrier G ==> e # x = x";
by (afs [thm "e_def", thm "binop_def"] 1);
val e_ax1 = result();

goal LocaleGroup.thy "!! x. x: carrier G ==> (x -|) # x = e";
by (afs [thm "binop_def", thm "inv_def", thm "e_def"] 1);
val inv_ax2 = result();

goal LocaleGroup.thy "!! x y z. [| x: carrier G; y: carrier G; z: carrier G |]\
\               ==> (x # y) # z = x # (y # z)";
by (afs [thm "binop_def"] 1);
val binop_assoc = result();

goal LocaleGroup.thy "!! G f i e1. [|f : G -> G -> G; i: G -> G; e1: G;\
\        ! x: G. (f (i x) x = e1); ! x: G. (f e1 x = x);\
\        ! x: G. ! y: G. ! z: G.(f (f x y) z = f (x) (f y z)) |] \
\ ==> (| carrier = G, bin_op = f, inverse = i, unit = e1 |) : Group";
by (afs [Group_def] 1);
val GroupI = result();

(*****)
(* Now the real derivations *)

goal LocaleGroup.thy "!! x y z. [| x : carrier G ; y : carrier G; z : carrier G;\
\                  x # y  =  x # z |] ==> y = z";
(* remarkable: In the following step the use of e_ax1 instead of unit_ax1
   is better! It doesn't produce G: Group as subgoal and the nice syntax stays *)
by (res_inst_tac [("P","%r. r = z")] (e_ax1 RS subst) 1);
by (assume_tac 1);
(* great: we can use the nice syntax even in res_inst_tac *)
by (res_inst_tac [("P","%r. r # y = z")] subst 1);
by (res_inst_tac [("x","x")] inv_ax2 1);
by (assume_tac 1);
by (stac binop_assoc 1);
by (rtac inv_closed 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (etac ssubst 1);
by (rtac (binop_assoc RS subst) 1);
by (rtac inv_closed 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (stac inv_ax2 1);
by (assume_tac 1);
by (stac e_ax1 1);
by (assume_tac 1);
by (rtac refl 1);
val left_cancellation = result();


(* here are the other directions of basic lemmas, they needed a cancellation (left) *)
(* to be able to show the other directions of inverse and unity axiom we need:*)
goal LocaleGroup.thy "!! x. x: carrier G ==> x # e = x";
(* here is a problem with res_inst_tac: in Fun there is a 
   constant inv, and that gets addressed when we type in -|.
   We have to use the defining term and then fold the def of inv *)
by (res_inst_tac [("x","inverse G x")] left_cancellation 1);
by (fold_goals_tac [thm "inv_def"]);
by (fast_tac (claset() addSEs [inv_closed]) 1);
by (afs [binop_closed, e_closed] 1);
by (assume_tac 1);
by (rtac (binop_assoc RS subst) 1);
by (fast_tac (claset() addSEs [inv_closed]) 1);
by (assume_tac 1);
by (rtac (e_closed) 1);
by (stac inv_ax2 1);
by (assume_tac 1);
by (stac e_ax1 1);
by (rtac e_closed 1);
by (rtac refl 1);
val e_ax2 = result();

goal LocaleGroup.thy "!! x. [| x: carrier G; x # x = x |] ==> x = e";
by (forw_inst_tac [("P","%y. x # x = y")] (e_ax2 RS forw_subst) 1);
by (assume_tac 1);
by (res_inst_tac [("x","x")] left_cancellation 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac e_closed 1);
by (assume_tac 1);
val idempotent_e = result();

goal LocaleGroup.thy  "!! x. x: carrier G ==> x # (x -|) = e";
by (rtac idempotent_e 1);
by (afs [binop_closed,inv_closed] 1);
by (stac binop_assoc 1);
by (assume_tac 1);
by (afs [inv_closed] 1);
by (afs [binop_closed,inv_closed] 1);
by (res_inst_tac [("t","x -| # x # x -|")] subst 1);
by (rtac binop_assoc 1);
by (afs [inv_closed] 1);
by (assume_tac 1);
by (afs [inv_closed] 1);
by (stac inv_ax2 1);
by (assume_tac 1);
by (stac e_ax1 1);
by (afs [inv_closed] 1);
by (rtac refl 1);
val inv_ax1 = result();


goal LocaleGroup.thy "!! x y. [| x: carrier G; y: carrier G; \
\                     x # y = e |] ==> y = x -|";
by (res_inst_tac [("x","x")] left_cancellation 1);
by (assume_tac 1);
by (assume_tac 1);
by (afs [inv_closed] 1);
by (stac inv_ax1 1);
by (assume_tac 1);
by (assume_tac 1);
val inv_unique = result();

goal LocaleGroup.thy "!! x. x : carrier G ==> x -| -| = x";
by (res_inst_tac [("x","inverse G x")] left_cancellation 1);
by (fold_goals_tac [thm "inv_def"]);
by (afs [inv_closed] 1);
by (afs [inv_closed] 1);
by (assume_tac 1);
by (afs [inv_ax1,inv_ax2,e_ax1,e_ax2,e_closed,inv_closed,binop_closed] 1);
val inv_inv = result();

goal LocaleGroup.thy "!! x y. [| x : carrier G; y : carrier G |]\
\           ==> (x # y) -| = y -| # x -|";
by (rtac sym 1);
by (rtac inv_unique 1);
by (afs [binop_closed] 1);
by (afs [inv_closed,binop_closed] 1);
by (afs [binop_assoc,inv_closed,binop_closed] 1);
by (res_inst_tac [("x1","y")] (binop_assoc RS subst) 1);
by (assume_tac 1);
by (afs [inv_closed] 1);
by (afs [inv_closed] 1);
by (afs [inv_ax1,inv_ax2,e_ax1,e_ax2,e_closed,inv_closed,binop_closed] 1);
val inv_prod = result();


goal LocaleGroup.thy "!! x y z. [| x : carrier G; y : carrier G;\
\ z : carrier G; y # x =  z # x|] ==> y = z";
by (res_inst_tac [("P","%r. r = z")] (e_ax2 RS subst) 1);
by (assume_tac 1);
by (res_inst_tac [("P","%r. y # r = z")] subst 1);
by (rtac inv_ax1 1);
by (assume_tac 1);
by (rtac (binop_assoc RS subst) 1);
by (assume_tac 1);
by (assume_tac 1);
by (afs [inv_closed] 1);
by (etac ssubst 1);
by (afs [binop_assoc,inv_closed,inv_ax1,e_ax2] 1);
val right_cancellation = result();

(* example what happens if export *)
val Left_cancellation = export left_cancellation;
