(*  Title:      HOL/LessThan/LessThan
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

lessThan, greaterThan, atLeast, atMost
*)


(*** Restrict [MOVE TO RELATION.THY??] ***)

Goalw [Restrict_def] "((x,y): Restrict A r) = ((x,y): r & x: A)";
by (Blast_tac 1);
qed "Restrict_iff";
AddIffs [Restrict_iff];

Goal "Restrict UNIV = id";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsimps [Restrict_def]));
qed "Restrict_UNIV";
Addsimps [Restrict_UNIV];

Goal "Restrict {} r = {}";
by (auto_tac (claset(), simpset() addsimps [Restrict_def]));
qed "Restrict_empty";
Addsimps [Restrict_empty];

Goalw [Restrict_def] "Restrict A (Restrict B r) = Restrict (A Int B) r";
by (Blast_tac 1);
qed "Restrict_Int";
Addsimps [Restrict_Int];

Goalw [Restrict_def] "Domain r <= A ==> Restrict A r = r";
by Auto_tac;
qed "Restrict_triv";

Goalw [Restrict_def] "Restrict A r <= r";
by Auto_tac;
qed "Restrict_subset";

Goalw [Restrict_def]
     "[| A <= B;  Restrict B r = Restrict B s |] \
\     ==> Restrict A r = Restrict A s";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "Restrict_eq_mono";

Goalw [Restrict_def, image_def]
     "[| s : RR;  Restrict A r = Restrict A s |] \
\     ==> Restrict A r : Restrict A `` RR";
by Auto_tac;
qed "Restrict_imageI";

Goal "Domain (Restrict A r) = A Int Domain r";
by (Blast_tac 1);
qed "Domain_Restrict";

Goal "(Restrict A r) ^^ B = r ^^ (A Int B)";
by (Blast_tac 1);
qed "Image_Restrict";

Addsimps [Domain_Restrict, Image_Restrict];



(*** lessThan ***)

Goalw [lessThan_def] "(i: lessThan k) = (i<k)";
by (Blast_tac 1);
qed "lessThan_iff";
AddIffs [lessThan_iff];

Goalw [lessThan_def] "lessThan 0 = {}";
by (Simp_tac 1);
qed "lessThan_0";
Addsimps [lessThan_0];

Goalw [lessThan_def] "lessThan (Suc k) = insert k (lessThan k)";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (Blast_tac 1);
qed "lessThan_Suc";

Goalw [lessThan_def, atMost_def] "lessThan (Suc k) = atMost k";
by (simp_tac (simpset() addsimps [less_Suc_eq_le]) 1);
qed "lessThan_Suc_atMost";

Goal "finite (lessThan k)";
by (induct_tac "k" 1);
by (simp_tac (simpset() addsimps [lessThan_Suc]) 2);
by Auto_tac;
qed "finite_lessThan";

Goal "(UN m. lessThan m) = UNIV";
by (Blast_tac 1);
qed "UN_lessThan_UNIV";

Goalw [lessThan_def, atLeast_def, le_def]
    "-lessThan k = atLeast k";
by (Blast_tac 1);
qed "Compl_lessThan";

Goal "{k} - lessThan k = {k}";
by (Blast_tac 1);
qed "single_Diff_lessThan";
Addsimps [single_Diff_lessThan];

(*** greaterThan ***)

Goalw [greaterThan_def] "(i: greaterThan k) = (k<i)";
by (Blast_tac 1);
qed "greaterThan_iff";
AddIffs [greaterThan_iff];

Goalw [greaterThan_def] "greaterThan 0 = range Suc";
by (blast_tac (claset() addIs [Suc_pred RS sym]) 1);
qed "greaterThan_0";
Addsimps [greaterThan_0];

Goalw [greaterThan_def] "greaterThan (Suc k) = greaterThan k - {Suc k}";
by (auto_tac (claset() addEs [linorder_neqE], simpset()));
qed "greaterThan_Suc";

Goal "(INT m. greaterThan m) = {}";
by (Blast_tac 1);
qed "INT_greaterThan_UNIV";

Goalw [greaterThan_def, atMost_def, le_def]
    "-greaterThan k = atMost k";
by (Blast_tac 1);
qed "Compl_greaterThan";

Goalw [greaterThan_def, atMost_def, le_def]
    "-atMost k = greaterThan k";
by (Blast_tac 1);
qed "Compl_atMost";

Goal "less_than ^^ {k} = greaterThan k";
by (Blast_tac 1);
qed "Image_less_than";

Addsimps [Compl_greaterThan, Compl_atMost, Image_less_than];

(*** atLeast ***)

Goalw [atLeast_def] "(i: atLeast k) = (k<=i)";
by (Blast_tac 1);
qed "atLeast_iff";
AddIffs [atLeast_iff];

Goalw [atLeast_def, UNIV_def] "atLeast 0 = UNIV";
by (Simp_tac 1);
qed "atLeast_0";
Addsimps [atLeast_0];

Goalw [atLeast_def] "atLeast (Suc k) = atLeast k - {k}";
by (simp_tac (simpset() addsimps [Suc_le_eq]) 1);
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (Blast_tac 1);
qed "atLeast_Suc";

Goal "(UN m. atLeast m) = UNIV";
by (Blast_tac 1);
qed "UN_atLeast_UNIV";

Goalw [lessThan_def, atLeast_def, le_def]
    "-atLeast k = lessThan k";
by (Blast_tac 1);
qed "Compl_atLeast";

Goal "less_than^-1 ^^ {k} = lessThan k";
by (Blast_tac 1);
qed "Image_inverse_less_than";

Addsimps [Compl_lessThan, Compl_atLeast, Image_inverse_less_than];

(*** atMost ***)

Goalw [atMost_def] "(i: atMost k) = (i<=k)";
by (Blast_tac 1);
qed "atMost_iff";
AddIffs [atMost_iff];

Goalw [atMost_def] "atMost 0 = {0}";
by (Simp_tac 1);
qed "atMost_0";
Addsimps [atMost_0];

Goalw [atMost_def] "atMost (Suc k) = insert (Suc k) (atMost k)";
by (simp_tac (simpset() addsimps [less_Suc_eq, order_le_less]) 1);
by (Blast_tac 1);
qed "atMost_Suc";

Goal "finite (atMost k)";
by (induct_tac "k" 1);
by (simp_tac (simpset() addsimps [atMost_Suc]) 2);
by Auto_tac;
qed "finite_atMost";

Goal "(UN m. atMost m) = UNIV";
by (Blast_tac 1);
qed "UN_atMost_UNIV";

Goalw [atMost_def, le_def]
    "-atMost k = greaterThan k";
by (Blast_tac 1);
qed "Compl_atMost";
Addsimps [Compl_atMost];


(*** Combined properties ***)

Goal "atMost n Int atLeast n = {n}";
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "atMost_Int_atLeast";




(*** Finally, a few set-theoretic laws...
     CAN BOOLEAN SIMPLIFICATION BE AUTOMATED? ***)

context Set.thy;

(** Rewrite rules to eliminate A.  Conditions can be satisfied by letting B
    be any set including A Int C and contained in A Un C, such as B=A or B=C.
**)

Goal "[| A Int C <= B; B <= A Un C |] \
\     ==> (A Int B) Un (-A Int C) = B Un C";
by (Blast_tac 1);
qed "set_cancel1";

Goal "[| A Int C <= B; B <= A Un C |] \
\     ==> (A Un B) Int (-A Un C) = B Int C";
by (Blast_tac 1);
qed "set_cancel2";

(*The base B=A*)
Goal "A Un (-A Int C) = A Un C";
by (Blast_tac 1);
qed "set_cancel3";

Goal "A Int (-A Un C) = A Int C";
by (Blast_tac 1);
qed "set_cancel4";

(*The base B=C*)
Goal "(A Int C) Un (-A Int C) = C";
by (Blast_tac 1);
qed "set_cancel5";

Goal "(A Un C) Int (-A Un C) = C";
by (Blast_tac 1);
qed "set_cancel6";

Addsimps [set_cancel1, set_cancel2, set_cancel3,
	  set_cancel4, set_cancel5, set_cancel6];


(** More ad-hoc rules **)

Goal "A Un B - (A - B) = B";
by (Blast_tac 1);
qed "Un_Diff_Diff";
Addsimps [Un_Diff_Diff];

Goal "A Int (B - C) Un C = A Int B Un C";
by (Blast_tac 1);
qed "Int_Diff_Un";

Goal "Union(B) Int A = (UN C:B. C Int A)";
by (Blast_tac 1);
qed "Int_Union2";

Goal "Union(B) Int A = Union((%C. C Int A)``B)";
by (Blast_tac 1);
qed "Int_Union_Union";

