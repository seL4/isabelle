(*  Title:      HOL/LessThan/LessThan
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

lessThan, greaterThan, atLeast, atMost
*)


open LessThan;


(*** lessThan ***)

goalw thy [lessThan_def] "(i: lessThan k) = (i<k)";
by (Blast_tac 1);
qed "lessThan_iff";
AddIffs [lessThan_iff];

goalw thy [lessThan_def] "lessThan 0 = {}";
by (Simp_tac 1);
qed "lessThan_0";
Addsimps [lessThan_0];

goalw thy [lessThan_def] "lessThan (Suc k) = insert k (lessThan k)";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (Blast_tac 1);
qed "lessThan_Suc";

goal thy "(UN m. lessThan m) = UNIV";
by (Blast_tac 1);
qed "UN_lessThan_UNIV";

goalw thy [lessThan_def, atLeast_def, le_def]
    "Compl(lessThan k) = atLeast k";
by (Blast_tac 1);
qed "Compl_lessThan";


(*** greaterThan ***)

goalw thy [greaterThan_def] "(i: greaterThan k) = (k<i)";
by (Blast_tac 1);
qed "greaterThan_iff";
AddIffs [greaterThan_iff];

goalw thy [greaterThan_def] "greaterThan 0 = range Suc";
by (blast_tac (claset() addIs [Suc_pred RS sym]) 1);
qed "greaterThan_0";
Addsimps [greaterThan_0];

goalw thy [greaterThan_def] "greaterThan (Suc k) = greaterThan k - {Suc k}";
by Safe_tac;
by (blast_tac (claset() addIs [less_trans]) 1);
by (asm_simp_tac (simpset() addsimps [le_Suc_eq, not_le_iff_less RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [not_le_iff_less]) 1);
qed "greaterThan_Suc";

goal thy "(INT m. greaterThan m) = {}";
by (Blast_tac 1);
qed "INT_greaterThan_UNIV";

goalw thy [greaterThan_def, atMost_def, le_def]
    "Compl(greaterThan k) = atMost k";
by (Blast_tac 1);
qed "Compl_greaterThan";

goalw thy [greaterThan_def, atMost_def, le_def]
    "Compl(atMost k) = greaterThan k";
by (Blast_tac 1);
qed "Compl_atMost";

goal thy "less_than ^^ {k} = greaterThan k";
by (Blast_tac 1);
qed "Image_less_than";

Addsimps [Compl_greaterThan, Compl_atMost, Image_less_than];

(*** atLeast ***)

goalw thy [atLeast_def] "(i: atLeast k) = (k<=i)";
by (Blast_tac 1);
qed "atLeast_iff";
AddIffs [atLeast_iff];

goalw thy [atLeast_def, UNIV_def] "atLeast 0 = UNIV";
by (Simp_tac 1);
qed "atLeast_0";
Addsimps [atLeast_0];

goalw thy [atLeast_def] "atLeast (Suc k) = atLeast k - {k}";
by (simp_tac (simpset() addsimps [Suc_le_eq]) 1);
by (simp_tac (simpset() addsimps [le_eq_less_or_eq]) 1);
by (Blast_tac 1);
qed "atLeast_Suc";

goal thy "(UN m. atLeast m) = UNIV";
by (Blast_tac 1);
qed "UN_atLeast_UNIV";

goalw thy [lessThan_def, atLeast_def, le_def]
    "Compl(atLeast k) = lessThan k";
by (Blast_tac 1);
qed "Compl_atLeast";

goal thy "less_than^-1 ^^ {k} = lessThan k";
by (Blast_tac 1);
qed "Image_inverse_less_than";

Addsimps [Compl_lessThan, Compl_atLeast, Image_inverse_less_than];

(*** atMost ***)

goalw thy [atMost_def] "(i: atMost k) = (i<=k)";
by (Blast_tac 1);
qed "atMost_iff";
AddIffs [atMost_iff];

goalw thy [atMost_def] "atMost 0 = {0}";
by (Simp_tac 1);
qed "atMost_0";
Addsimps [atMost_0];

goalw thy [atMost_def] "atMost (Suc k) = insert (Suc k) (atMost k)";
by (simp_tac (simpset() addsimps [less_Suc_eq, le_eq_less_or_eq]) 1);
by (Blast_tac 1);
qed "atMost_Suc";

goal thy "(UN m. atMost m) = UNIV";
by (Blast_tac 1);
qed "UN_atMost_UNIV";

goalw thy [atMost_def, le_def]
    "Compl(atMost k) = greaterThan k";
by (Blast_tac 1);
qed "Compl_atMost";
Addsimps [Compl_atMost];


(*** Combined properties ***)

goal thy "atMost n Int atLeast n = {n}";
by (blast_tac (claset() addIs [le_anti_sym]) 1);
qed "atMost_Int_atLeast";


