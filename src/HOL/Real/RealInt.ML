(*  Title:       RealInt.ML
    ID:         $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   1999 University of Edinburgh
    Description: Embedding the integers in the reals
*)


Goalw [congruent_def]
  "congruent intrel (%p. (%(i,j). realrel `` \
\  {(preal_of_prat (prat_of_pnat (pnat_of_nat i)), \
\    preal_of_prat (prat_of_pnat (pnat_of_nat j)))}) p)";
by (auto_tac (claset(),
	      simpset() addsimps [pnat_of_nat_add, prat_of_pnat_add RS sym,
				  preal_of_prat_add RS sym]));
qed "real_of_int_congruent";

Goalw [real_of_int_def]
   "real (Abs_Integ (intrel `` {(i, j)})) = \
\     Abs_REAL(realrel `` \
\       {(preal_of_prat (prat_of_pnat (pnat_of_nat i)), \
\         preal_of_prat (prat_of_pnat (pnat_of_nat j)))})";
by (res_inst_tac [("f","Abs_REAL")] arg_cong 1);
by (simp_tac (simpset() addsimps [realrel_in_real RS Abs_REAL_inverse,
		[equiv_intrel, real_of_int_congruent] MRS UN_equiv_class]) 1);
qed "real_of_int";

Goal "inj(real :: int => real)";
by (rtac injI 1);
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset() addSDs [inj_preal_of_prat RS injD,
			   inj_prat_of_pnat RS injD, inj_pnat_of_nat RS injD],
	      simpset() addsimps [real_of_int,preal_of_prat_add RS sym,
				  prat_of_pnat_add RS sym,pnat_of_nat_add]));
qed "inj_real_of_int";

Goalw [int_def,real_zero_def] "real (int 0) = 0";
by (simp_tac (simpset() addsimps [real_of_int, preal_add_commute]) 1);
qed "real_of_int_zero";

Goalw [int_def,real_one_def] "real (int 1) = 1r";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_int,
				  preal_of_prat_add RS sym,pnat_two_eq,
			       prat_of_pnat_add RS sym,pnat_one_iff RS sym]));
qed "real_of_int_one";

Goal "real (x::int) + real y = real (x + y)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset(),
     simpset() addsimps [real_of_int, preal_of_prat_add RS sym,
                         prat_of_pnat_add RS sym, zadd,real_add,
                         pnat_of_nat_add] @ pnat_add_ac));
qed "real_of_int_add";
Addsimps [real_of_int_add RS sym];

Goal "-real (x::int) = real (-x)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (auto_tac (claset(), simpset() addsimps [real_of_int, real_minus,zminus]));
qed "real_of_int_minus";
Addsimps [real_of_int_minus RS sym];

Goalw [zdiff_def,real_diff_def]
  "real (x::int) - real y = real (x - y)";
by (simp_tac (HOL_ss addsimps [real_of_int_add, real_of_int_minus]) 1);
qed "real_of_int_diff";
Addsimps [real_of_int_diff RS sym];

Goal "real (x::int) * real y = real (x * y)";
by (res_inst_tac [("z","x")] eq_Abs_Integ 1);
by (res_inst_tac [("z","y")] eq_Abs_Integ 1);
by (auto_tac (claset(),
   simpset() addsimps [real_of_int, real_mult,zmult,
		       preal_of_prat_mult RS sym,pnat_of_nat_mult,
		       prat_of_pnat_mult RS sym,preal_of_prat_add RS sym,
		       prat_of_pnat_add RS sym,pnat_of_nat_add] @ 
                      mult_ac @ add_ac @ pnat_add_ac));
qed "real_of_int_mult";
Addsimps [real_of_int_mult RS sym];

Goal "real (int (Suc n)) = real (int n) + 1r";
by (simp_tac (simpset() addsimps [real_of_int_one RS sym, zadd_int] @ 
                                 zadd_ac) 1);
qed "real_of_int_Suc";

(* relating two of the embeddings *)
Goal "real (int n) = real n";
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (HOL_ss addsimps [real_of_int_zero, real_of_nat_zero,
                                         real_of_int_Suc,real_of_nat_Suc])));
by (Simp_tac 1);
qed "real_of_int_real_of_nat";

Goal "~neg z ==> real (nat z) = real z";
by (asm_simp_tac (simpset() addsimps [not_neg_nat,
				      real_of_int_real_of_nat RS sym]) 1);
qed "real_of_nat_real_of_int";

Goal "(real x = 0) = (x = int 0)";
by (auto_tac (claset() addIs [inj_real_of_int RS injD],
	      HOL_ss addsimps [real_of_int_zero]));
qed "real_of_int_zero_cancel";
Addsimps [real_of_int_zero_cancel];

Goal "real (x::int) < real y ==> x < y";
by (rtac ccontr 1 THEN dtac (linorder_not_less RS iffD1) 1);
by (auto_tac (claset(),
	      simpset() addsimps [zle_iff_zadd, real_of_int_add RS sym,
				  real_of_int_real_of_nat,
				  linorder_not_le RS sym]));
qed "real_of_int_less_cancel";

Goal "(real (x::int) = real y) = (x = y)";
by (blast_tac (claset() addSDs [inj_real_of_int RS injD]) 1);
qed "real_of_int_inject";
AddIffs [real_of_int_inject];

Goal "x < y ==> (real (x::int) < real y)";
by (full_simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1);
by (auto_tac (claset() addSDs [real_of_int_less_cancel],
	      simpset() addsimps [order_le_less]));
qed "real_of_int_less_mono";

Goal "(real (x::int) < real y) = (x < y)";
by (blast_tac (claset() addDs [real_of_int_less_cancel]
			addIs [real_of_int_less_mono]) 1);
qed "real_of_int_less_iff";
AddIffs [real_of_int_less_iff];

Goal "(real (x::int) <= real y) = (x <= y)";
by (full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "real_of_int_le_iff";
Addsimps [real_of_int_le_iff];
