(*  Title:      HOL/ex/LocaleGroup.ML
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Group theory via records and locales.
*)

Open_locale "groups";
print_locales LocaleGroup.thy;

val simp_G = simplify (simpset() addsimps [Group_def]) (thm "Group_G");
Addsimps [simp_G, thm "Group_G"];


Goal "e : carrier G";
by (simp_tac (simpset() addsimps [thm "e_def"]) 1);
qed "e_closed";

(* Mit dieser Def ist es halt schwierig *)
Goal "op # : carrier G -> carrier G -> carrier G";
by (res_inst_tac [("t","op #")] ssubst 1);
by (rtac ext 1);
by (rtac ext 1);
by (rtac meta_eq_to_obj_eq 1);
by (rtac (thm "binop_def") 1);
by (Asm_full_simp_tac 1);
qed "binop_funcset";

Goal "[| x: carrier G; y: carrier G |] ==> x # y : carrier G";
by (asm_simp_tac
    (simpset() addsimps [binop_funcset RS funcset_mem RS funcset_mem]) 1);
qed "binop_closed";

Addsimps [binop_closed, e_closed];

Goal "INV : carrier G -> carrier G";
by (asm_simp_tac (simpset() addsimps [thm "inv_def"]) 1);
qed "inv_funcset";

Goal "x: carrier G ==> i(x) : carrier G";
by (asm_simp_tac (simpset() addsimps [inv_funcset RS funcset_mem]) 1);
qed "inv_closed"; 

Goal "x: carrier G ==> e # x = x";
by (asm_simp_tac (simpset() addsimps [thm "e_def", thm "binop_def"]) 1);
qed "e_ax1";

Goal "x: carrier G ==> i(x) # x = e";
by (asm_simp_tac
    (simpset() addsimps [thm "binop_def", thm "inv_def", thm "e_def"]) 1);
qed "inv_ax2";

Addsimps [inv_closed, e_ax1, inv_ax2];

Goal "[| x: carrier G; y: carrier G; z: carrier G |]\
\               ==> (x # y) # z = x # (y # z)";
by (asm_simp_tac (simpset() addsimps [thm "binop_def"]) 1);
qed "binop_assoc";

Goal "[|f : A -> A -> A; i: A -> A; e1: A;\
\        ! x: A. (f (i x) x = e1); ! x: A. (f e1 x = x);\
\        ! x: A. ! y: A. ! z: A.(f (f x y) z = f (x) (f y z)) |] \
\     ==> (| carrier = A, bin_op = f, inverse = i, unit = e1 |) : Group";
by (asm_simp_tac (simpset() addsimps [Group_def]) 1);
qed "GroupI";

(*****)
(* Now the real derivations *)

Goal "[| x # y  =  x # z;  \
\        x : carrier G ; y : carrier G; z : carrier G |] ==> y = z";
by (res_inst_tac [("P","%r. r = z")] (e_ax1 RS subst) 1);
by (assume_tac 1);
(* great: we can use the nice syntax even in res_inst_tac *)
by (res_inst_tac [("P","%r. r # y = z")] (inv_ax2 RS subst) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() delsimps [inv_ax2] addsimps [binop_assoc]) 1);
by (asm_simp_tac (simpset() addsimps [binop_assoc RS sym]) 1);
qed "left_cancellation";


(* Here are the other directions of basic lemmas. 
   They needed a cancellation (left) to be able to show the other
   directions of inverse and unity axiom.*)
Goal "x: carrier G ==> x # e = x";
by (rtac left_cancellation 1);
by (etac inv_closed 2);
by (auto_tac (claset(), simpset() addsimps [binop_assoc RS sym]));
qed "e_ax2";

Addsimps [e_ax2];

Goal "[| x: carrier G; x # x = x |] ==> x = e";
by (forw_inst_tac [("P","%y. x # x = y")] (e_ax2 RS ssubst) 1);
by (etac left_cancellation 2);
by Auto_tac;
qed "idempotent_e";

Goal  "x: carrier G ==> x # i(x) = e";
by (rtac idempotent_e 1);
by (Asm_simp_tac 1);
by (subgoal_tac "(x # i(x)) # x # i(x) = x # (i(x) # x) # i(x)" 1);
by (asm_simp_tac (simpset() delsimps [inv_ax2]
			    addsimps [binop_assoc]) 2);
by Auto_tac;
qed "inv_ax1";

Addsimps [inv_ax1];

Goal "[| x # y = e; x: carrier G; y: carrier G |] ==> y = i(x)";
by (res_inst_tac [("x","x")] left_cancellation 1);
by Auto_tac;
qed "inv_unique";

Goal "x : carrier G ==> i(i(x)) = x";
by (res_inst_tac [("x","i(x)")] left_cancellation 1);
by Auto_tac;
qed "inv_inv";

Addsimps [inv_inv];

Goal "[| x : carrier G; y : carrier G |] ==> i(x # y) = i(y) # i(x)";
by (rtac (inv_unique RS sym) 1);
by (subgoal_tac "(x # y) # i(y) # i(x) = x # (y # i(y)) # i(x)" 1);
by (asm_simp_tac (simpset() delsimps [inv_ax1, inv_ax2]
			    addsimps [binop_assoc]) 2);
by Auto_tac;
qed "inv_prod";


Goal "[| y # x = z # x;  x : carrier G; y : carrier G; \
\        z : carrier G |] ==> y = z";
by (res_inst_tac [("P","%r. r = z")] (e_ax2 RS subst) 1);
by (assume_tac 1);
by (res_inst_tac [("P","%r. y # r = z")] (inv_ax1 RS subst) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() delsimps [inv_ax1] 
		  addsimps [binop_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [binop_assoc]) 1);
qed "right_cancellation";

Close_locale "groups";

(* example what happens if export *)
val Left_cancellation = export left_cancellation;
