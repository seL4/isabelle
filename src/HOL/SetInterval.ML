(*  Title:      HOL/SetInterval.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000  TU Muenchen

Set Intervals: lessThan, greaterThan, atLeast, atMost
*)


(*** lessThan ***)

Goalw [lessThan_def] "(i: lessThan k) = (i<k)";
by (Blast_tac 1);
qed "lessThan_iff";
AddIffs [lessThan_iff];

Goalw [lessThan_def] "lessThan (0::nat) = {}";
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

Goal "(UN m::nat. lessThan m) = UNIV";
by (Blast_tac 1);
qed "UN_lessThan_UNIV";

Goalw [lessThan_def, atLeast_def]
    "!!k:: 'a::linorder. -lessThan k = atLeast k";
by Auto_tac;
by (blast_tac (claset() addIs [linorder_not_less RS iffD1]) 1);
by (blast_tac (claset() addIs [order_le_less_trans RS 
	                       (order_less_irrefl RS notE)]) 1);
qed "Compl_lessThan";

Goal "!!k:: 'a::order. {k} - lessThan k = {k}";
by Auto_tac;
qed "single_Diff_lessThan";
Addsimps [single_Diff_lessThan];

(*** greaterThan ***)

Goalw [greaterThan_def] "(i: greaterThan k) = (k<i)";
by (Blast_tac 1);
qed "greaterThan_iff";
AddIffs [greaterThan_iff];

Goalw [greaterThan_def] "greaterThan 0 = range Suc";
by (blast_tac (claset() addDs [gr0_conv_Suc RS iffD1]) 1);
qed "greaterThan_0";
Addsimps [greaterThan_0];

Goalw [greaterThan_def] "greaterThan (Suc k) = greaterThan k - {Suc k}";
by (auto_tac (claset() addEs [linorder_neqE], simpset()));
qed "greaterThan_Suc";

Goal "(INT m::nat. greaterThan m) = {}";
by (Blast_tac 1);
qed "INT_greaterThan_UNIV";

Goalw [greaterThan_def, atMost_def, le_def]
    "!!k:: 'a::linorder. -greaterThan k = atMost k";
by Auto_tac;
by (blast_tac (claset() addIs [linorder_not_less RS iffD1]) 1);
by (blast_tac (claset() addIs [order_le_less_trans RS 
	                       (order_less_irrefl RS notE)]) 1);
qed "Compl_greaterThan";

Goal "!!k:: 'a::linorder. -atMost k = greaterThan k";
by (simp_tac (simpset() addsimps [Compl_greaterThan RS sym]) 1);
qed "Compl_atMost";

Addsimps [Compl_greaterThan, Compl_atMost];

(*** atLeast ***)

Goalw [atLeast_def] "(i: atLeast k) = (k<=i)";
by (Blast_tac 1);
qed "atLeast_iff";
AddIffs [atLeast_iff];

Goalw [atLeast_def, UNIV_def] "atLeast (0::nat) = UNIV";
by (Simp_tac 1);
qed "atLeast_0";
Addsimps [atLeast_0];

Goalw [atLeast_def] "atLeast (Suc k) = atLeast k - {k}";
by (simp_tac (simpset() addsimps [Suc_le_eq]) 1);
by (simp_tac (simpset() addsimps [order_le_less]) 1);
by (Blast_tac 1);
qed "atLeast_Suc";

Goal "(UN m::nat. atLeast m) = UNIV";
by (Blast_tac 1);
qed "UN_atLeast_UNIV";

Goalw [lessThan_def, atLeast_def, le_def]
    "!!k:: 'a::linorder. -atLeast k = lessThan k";
by Auto_tac;
by (blast_tac (claset() addIs [linorder_not_less RS iffD1]) 1);
by (blast_tac (claset() addIs [order_le_less_trans RS 
	                       (order_less_irrefl RS notE)]) 1);
qed "Compl_atLeast";

Addsimps [Compl_lessThan, Compl_atLeast];

(*** atMost ***)

Goalw [atMost_def] "(i: atMost k) = (i<=k)";
by (Blast_tac 1);
qed "atMost_iff";
AddIffs [atMost_iff];

Goalw [atMost_def] "atMost (0::nat) = {0}";
by (Simp_tac 1);
qed "atMost_0";
Addsimps [atMost_0];

Goalw [atMost_def] "atMost (Suc k) = insert (Suc k) (atMost k)";
by (simp_tac (simpset() addsimps [less_Suc_eq, order_le_less]) 1);
by (Blast_tac 1);
qed "atMost_Suc";

Goal "(UN m::nat. atMost m) = UNIV";
by (Blast_tac 1);
qed "UN_atMost_UNIV";


(*** Combined properties ***)

Goal "!!n:: 'a::order. atMost n Int atLeast n = {n}";
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "atMost_Int_atLeast";
