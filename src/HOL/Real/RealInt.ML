(*  Title:       RealInt.ML
    ID:         $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   1999 University of Edinburgh
    Description: Embedding the integers in the reals
*)


Goalw [congruent_def]
  "congruent intrel (%p. split (%i j. realrel ^^ \
\  {(preal_of_prat (prat_of_pnat (pnat_of_nat i)), \
\    preal_of_prat (prat_of_pnat (pnat_of_nat j)))}) p)";
by (auto_tac (claset(),simpset() addsimps [pnat_of_nat_add,
    prat_of_pnat_add RS sym,preal_of_prat_add RS sym]));
qed "real_of_int_congruent";

val real_of_int_ize = RSLIST [equiv_intrel, real_of_int_congruent];

Goalw [real_of_int_def]
   "real_of_int (Abs_Integ (intrel ^^ {(i, j)})) = \
\     Abs_real(realrel ^^ \
\       {(preal_of_prat (prat_of_pnat (pnat_of_nat i)), \
\         preal_of_prat (prat_of_pnat (pnat_of_nat j)))})";
by (res_inst_tac [("f","Abs_real")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [realrel_in_real RS Abs_real_inverse,
    real_of_int_ize UN_equiv_class]) 1);
qed "real_of_int";

Goal "inj(real_of_int)";
by (rtac injI 1);
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset() addSDs [inj_preal_of_prat RS injD,
    inj_prat_of_pnat RS injD,inj_pnat_of_nat RS injD],
    simpset() addsimps [real_of_int,preal_of_prat_add RS sym,
     prat_of_pnat_add RS sym,pnat_of_nat_add]));
qed "inj_real_of_int";

Goalw [int_def,real_zero_def] "real_of_int (int 0) = 0r";
by (simp_tac (simpset() addsimps [real_of_int, preal_add_commute]) 1);
qed "real_of_int_zero";

Goalw [int_def,real_one_def] "real_of_int (int 1) = 1r";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_int,
				  preal_of_prat_add RS sym,pnat_two_eq,
			       prat_of_pnat_add RS sym,pnat_one_iff RS sym]));
qed "real_of_int_one";

Goal "real_of_int x + real_of_int y = real_of_int (x + y)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset(),simpset() addsimps [real_of_int,
    preal_of_prat_add RS sym,prat_of_pnat_add RS sym,
    zadd,real_add,pnat_of_nat_add] @ pnat_add_ac));
qed "real_of_int_add";

Goal "-real_of_int x = real_of_int (-x)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (auto_tac (claset(),simpset() addsimps [real_of_int,
    real_minus,zminus]));
qed "real_of_int_minus";

Goalw [zdiff_def,real_diff_def]
  "real_of_int x - real_of_int y = real_of_int (x - y)";
by (simp_tac (simpset() addsimps [real_of_int_add,
    real_of_int_minus]) 1);
qed "real_of_int_diff";

Goal "real_of_int x * real_of_int y = real_of_int (x * y)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset(),simpset() addsimps [real_of_int,
    real_mult,zmult,preal_of_prat_mult RS sym,pnat_of_nat_mult,
    prat_of_pnat_mult RS sym,preal_of_prat_add RS sym,
    prat_of_pnat_add RS sym,pnat_of_nat_add] @ mult_ac @add_ac 
    @ pnat_add_ac));
qed "real_of_int_mult";

Goal "real_of_int (int (Suc n)) = real_of_int (int n) + 1r";
by (simp_tac (simpset() addsimps [real_of_int_one RS sym,
				  real_of_int_add,zadd_int]) 1);
qed "real_of_int_Suc";

(* relating two of the embeddings *)
Goal "real_of_int (int n) = real_of_nat n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [real_of_int_zero,
    real_of_nat_zero,real_of_int_Suc,real_of_nat_Suc]));
qed "real_of_int_real_of_nat";

Goal "~neg z ==> real_of_nat (nat z) = real_of_int z";
by (asm_simp_tac (simpset() addsimps [not_neg_nat,
    real_of_int_real_of_nat RS sym]) 1);
qed "real_of_nat_real_of_int";

(* put with other properties of real_of_nat? *)
Goal "neg z ==> real_of_nat (nat z) = 0r";
by (asm_simp_tac (simpset() addsimps [neg_nat,
    real_of_nat_zero]) 1);
qed "real_of_nat_neg_int";
Addsimps [real_of_nat_neg_int];

Goal "(real_of_int x = 0r) = (x = int 0)";
by (auto_tac (claset() addIs [inj_real_of_int RS injD],
    simpset() addsimps [real_of_int_zero]));
qed "real_of_int_zero_cancel";
Addsimps [real_of_int_zero_cancel];

Goal "real_of_int x < real_of_int y ==> x < y";
by (rtac ccontr 1 THEN dtac (linorder_not_less RS iffD1) 1);
by (auto_tac (claset(),
	      simpset() addsimps [zle_iff_zadd, real_of_int_add RS sym,
				  real_of_int_real_of_nat,
				  real_of_nat_zero RS sym]));
qed "real_of_int_less_cancel";

Goal "x < y ==> (real_of_int x < real_of_int y)";
by (auto_tac (claset(),
	      simpset() addsimps [zless_iff_Suc_zadd, real_of_int_add RS sym,
				  real_of_int_real_of_nat,
				  real_of_nat_Suc]));
by (simp_tac (simpset() addsimps [real_of_nat_one RS
    sym,real_of_nat_zero RS sym,real_of_nat_add]) 1); 
qed "real_of_int_less_mono";

Goal "(real_of_int x < real_of_int y) = (x < y)";
by (auto_tac (claset() addIs [real_of_int_less_cancel,
			      real_of_int_less_mono],
	      simpset()));
qed "real_of_int_less_iff";
Addsimps [real_of_int_less_iff];

Goal "(real_of_int x <= real_of_int y) = (x <= y)";
by (auto_tac (claset(),
	      simpset() addsimps [real_le_def, zle_def]));
qed "real_of_int_le_iff";
Addsimps [real_of_int_le_iff];

Goal "(real_of_int x = real_of_int y) = (x = y)";
by (auto_tac (claset() addSIs [order_antisym],
	      simpset() addsimps [real_of_int_le_iff RS iffD1]));
qed "real_of_int_eq_iff";
Addsimps [real_of_int_eq_iff];
