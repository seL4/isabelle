(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Group theory using locales
*)


fun afs thms = (asm_full_simp_tac (simpset() addsimps thms));


(* Proof of group theory theorems necessary for Sylow's theorem *)
Open_locale "group";

val e_def = thm "e_def";
val binop_def = thm "binop_def";
val inv_def = thm "inv_def";
val Group_G = thm "Group_G";


val simp_G = simplify (simpset() addsimps [Group_def]) (Group_G);
Addsimps [simp_G, Group_G];

Goal "e \\<in> carrier G";
by (afs [e_def] 1);
qed "e_closed";
val unit_closed = export e_closed;
Addsimps [e_closed];

Goal "op ## \\<in> carrier G \\<rightarrow> carrier G \\<rightarrow> carrier G";
by (simp_tac (simpset() addsimps [binop_def]) 1); 
qed "binop_funcset";

Goal "[| x \\<in> carrier G; y \\<in> carrier G |] ==> x ## y \\<in> carrier G";
by (afs [binop_funcset RS (funcset_mem RS funcset_mem)] 1);
qed "binop_closed";
val bin_op_closed = export binop_closed;
Addsimps [binop_closed];

Goal "INV \\<in> carrier G \\<rightarrow> carrier G";
by (simp_tac (simpset() addsimps [inv_def]) 1); 
qed "inv_funcset";

Goal "x \\<in> carrier G ==> i(x) \\<in> carrier G";
by (afs [inv_funcset RS funcset_mem] 1);
qed "inv_closed"; 
val inverse_closed = export inv_closed;
Addsimps [inv_closed];

Goal "x \\<in> carrier G ==> e ## x = x";
by (afs [e_def, binop_def] 1);
qed "e_ax1";
Addsimps [e_ax1];

Goal "x \\<in> carrier G ==> i(x) ## x = e";
by (afs [binop_def, inv_def, e_def] 1);
qed "inv_ax2";
Addsimps [inv_ax2]; 

Goal "[| x \\<in> carrier G; y \\<in> carrier G; z \\<in> carrier G |] \
\     ==> (x ## y) ## z = x ## (y ## z)";
by (afs [binop_def] 1);
qed "binop_assoc";

Goal "[|f \\<in> A \\<rightarrow> A \\<rightarrow> A;  i1 \\<in> A \\<rightarrow> A;  e1 \\<in> A;\
\       \\<forall>x \\<in> A. (f (i1 x) x = e1);  \\<forall>x \\<in> A. (f e1 x = x);\
\       \\<forall>x \\<in> A. \\<forall>y \\<in> A. \\<forall>z \\<in> A. (f (f x y) z = f (x) (f y z)) |] \
\     ==> (| carrier = A, bin_op = f, inverse = i1, unit = e1 |) \\<in> Group";
by (afs [Group_def] 1);
qed "groupI";
val GroupI = export groupI;

(*****)
(* Now the real derivations *)

Goal "[| x\\<in>carrier G ; y\\<in>carrier G; z\\<in>carrier G;  x ## y  =  x ## z |] \
\     ==> y = z";
by (dres_inst_tac [("f","%z. i x ## z")] arg_cong 1); 
by (asm_full_simp_tac (simpset() addsimps [binop_assoc RS sym]) 1); 
qed "left_cancellation";

Goal "[| x \\<in> carrier G; y \\<in> carrier G; z \\<in> carrier G |] \
\     ==> (x ## y  =  x ## z) = (y = z)";
by (blast_tac (claset() addIs [left_cancellation]) 1); 
qed "left_cancellation_iff";


(* Now the other directions of basic lemmas; they need a left cancellation*)

Goal "x \\<in> carrier G ==> x ## e = x";
by (res_inst_tac [("x","i x")] left_cancellation 1);
by (auto_tac (claset(), simpset() addsimps [binop_assoc RS sym])); 
qed "e_ax2";
Addsimps [e_ax2];

Goal "[| x \\<in> carrier G; x ## x = x |] ==> x = e";
by (res_inst_tac [("x","x")] left_cancellation 1);
by Auto_tac; 
qed "idempotent_e";

Goal  "x \\<in> carrier G ==> x ## i(x) = e";
by (rtac idempotent_e 1);
by (auto_tac (claset(), simpset() addsimps [binop_assoc RS sym]));
by (asm_simp_tac (simpset() addsimps [inst "x" "x" binop_assoc]) 1); 
qed "inv_ax1";
Addsimps [inv_ax1]; 

Goal "[| x \\<in> carrier G; y \\<in> carrier G; x ## y = e |] ==> y = i(x)";
by (res_inst_tac [("x","x")] left_cancellation 1);
by Auto_tac; 
qed "inv_unique";

Goal "x \\<in> carrier G ==> i(i(x)) = x";
by (res_inst_tac [("x","i x")] left_cancellation 1);
by Auto_tac; 
qed "inv_inv";
Addsimps [inv_inv]; 

Goal "[| x \\<in> carrier G; y \\<in> carrier G |] ==> i(x ## y) = i(y) ## i(x)";
by (rtac (inv_unique RS sym) 1);
by (auto_tac (claset(), simpset() addsimps [binop_assoc RS sym]));
by (asm_simp_tac (simpset() addsimps [inst "x" "x" binop_assoc]) 1); 
qed "inv_prod";

Goal "[| y ## x =  z ## x;  \
\        x \\<in> carrier G; y \\<in> carrier G; z \\<in> carrier G|] ==> y = z";
by (dres_inst_tac [("f","%z. z ## i x")] arg_cong 1); 
by (asm_full_simp_tac (simpset() addsimps [binop_assoc]) 1); 
qed "right_cancellation";

Goal "[| x \\<in> carrier G; y \\<in> carrier G; z \\<in> carrier G |] \
\     ==> (y ## x =  z ## x) = (y = z)";
by (blast_tac (claset() addIs [right_cancellation]) 1); 
qed "right_cancellation_iff";


(* subgroup *)
Goal "[| H <= carrier G; H \\<noteq> {}; \\<forall>a \\<in> H. i(a)\\<in>H; \\<forall>a\\<in>H. \\<forall>b\\<in>H. a ## b\\<in>H|] \
\     ==> e \\<in> H";
by (Force_tac 1); 
qed "e_in_H";

(* subgroupI: a characterization of subgroups *)
Goal "[| H <= carrier G; H \\<noteq> {}; \\<forall>a \\<in> H. i(a)\\<in>H;\
\          \\<forall>a\\<in>H. \\<forall>b\\<in>H. a ## b\\<in>H |] ==> H <<= G";
by (asm_full_simp_tac (simpset() addsimps [subgroup_def]) 1); 
(* Fold the locale definitions: the top level definition of subgroup gives
   the verbose form, which does not immediately match rules like inv_ax1 *)
by (rtac groupI 1);
by (ALLGOALS (asm_full_simp_tac
    (simpset() addsimps [subsetD, restrictI, e_in_H, binop_assoc] @
                        (map symmetric [binop_def, inv_def, e_def]))));
qed "subgroupI";
val SubgroupI = export subgroupI;

Goal "H <<= G  ==> \
\      (|carrier = H, bin_op = lam x:H. lam y:H. x ## y, \
\       inverse = lam x:H. i(x), unit = e|)\\<in>Group";
by (afs [subgroup_def, binop_def, inv_def, e_def] 1);
qed "subgroupE2";
val SubgroupE2 = export subgroupE2;

Goal "H <<= G  ==> H <= carrier G";
by (afs [subgroup_def, binop_def, inv_def, e_def] 1);
qed "subgroup_imp_subset";

Goal "[| H <<= G; x \\<in> H; y \\<in> H |] ==> x ## y \\<in> H";
by (dtac subgroupE2 1);
by (dtac bin_op_closed 1);
by (Asm_full_simp_tac 1);
by (thin_tac "x\\<in>H" 1);
by Auto_tac; 
qed "subgroup_f_closed";

Goal "[| H <<= G; x \\<in> H |] ==> i x \\<in> H";
by (dtac (subgroupE2 RS inverse_closed) 1);
by Auto_tac; 
qed "subgroup_inv_closed";
val Subgroup_inverse_closed = export subgroup_inv_closed;

Goal "H <<= G ==> e\\<in>H";
by (dtac (subgroupE2 RS unit_closed) 1);
by (Asm_full_simp_tac 1);
qed "subgroup_e_closed";

Goal "[| finite(carrier G); H <<= G |] ==> 0 < card(H)";
by (subgoal_tac "finite H" 1);
 by (blast_tac (claset() addIs [finite_subset] addDs [subgroup_imp_subset]) 2);
by (rtac ccontr 1); 
by (asm_full_simp_tac (simpset() addsimps [card_0_eq]) 1); 
by (blast_tac (claset() addDs [subgroup_e_closed]) 1); 
qed "SG_card1";

(* Abelian Groups *) 
Goal "[|G' \\<in> AbelianGroup; x: carrier G'; y: carrier G'|]  \
\     ==> (G'.<f>) x y = (G'.<f>) y x";
by (auto_tac (claset(), simpset() addsimps [AbelianGroup_def])); 
qed "Group_commute";

Goal "AbelianGroup <= Group";
by (auto_tac (claset(), simpset() addsimps [AbelianGroup_def])); 
qed "Abel_subset_Group";

val Abel_imp_Group = Abel_subset_Group RS subsetD;

Close_locale "group";
