(*  Title:      ZF/IMP/Denotation.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

(** Rewrite Rules for A,B,C **)
Addsimps [A_nat_def,A_loc_def,A_op1_def,A_op2_def];
Addsimps [B_true_def,B_false_def,B_op_def,B_not_def,B_and_def,B_or_def];
Addsimps [C_skip_def,C_assign_def,C_comp_def,C_if_def,C_while_def]; 

(** Type_intr for A **)

Goal "[|a:aexp; sigma:loc->nat|] ==> A(a,sigma):nat";
by (etac aexp.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (claset() addSIs [apply_type])));
qed "A_type";

(** Type_intr for B **)

Goal "[|b:bexp; sigma:loc->nat|] ==> B(b,sigma):bool";
by (etac bexp.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (claset() addSIs [apply_type,A_type]@bool_typechecks)));
qed "B_type";

(** C_subset **)

Goal "c:com ==> C(c) <= (loc->nat)*(loc->nat)";
by (etac com.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (claset() addDs [lfp_subset RS subsetD])));
qed "C_subset";

(** Type_elims for C **)

Goal "[| <x,y>:C(c); c:com |] ==> x:loc->nat & y:loc->nat";
by (blast_tac (claset() addDs [C_subset RS subsetD]) 1);
qed "C_type_D";

Goal "[| x:C(c); c:com |] ==> fst(x):loc->nat";
by (dtac (C_subset RS subsetD) 1);
by (atac 1);
by (etac SigmaE 1);
by (Asm_simp_tac 1);
qed "C_type_fst";

AddDs [C_type_D, C_type_fst];

(** bnd_mono (nat->nat*nat->nat,Gamma(b,c) **)

Goalw [bnd_mono_def,Gamma_def]
     "c:com ==> bnd_mono ((loc->nat)*(loc->nat),Gamma(b,c))";
by (Blast_tac 1);
qed "Gamma_bnd_mono";

(** End ***)
