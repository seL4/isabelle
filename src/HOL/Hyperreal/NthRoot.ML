(*  Title       : NthRoot.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Existence of nth root. Adapted from
                   http://www.math.unl.edu/~webnotes
*)

(*----------------------------------------------------------------------
                         Existence of nth root
   Various lemmas needed for this result. We follow the proof
   given by John Lindsay Orr (jorr@math.unl.edu) in his Analysis
   Webnotes available on the www at http://www.math.unl.edu/~webnotes
   Lemmas about sequences of reals are used to reach the result.
 ---------------------------------------------------------------------*)

Goal "[| (0::real) < a; 0 < n |] \
\     ==> EX s. s : {x. x ^ n <= a & 0 < x}";
by (case_tac "1 <= a" 1);
by (res_inst_tac [("x","1")] exI 1);
by (dtac not_real_leE 2);
by (dtac (less_not_refl2 RS  not0_implies_Suc) 2);
by (auto_tac (claset() addSIs [realpow_Suc_le_self],
    simpset() addsimps [real_zero_less_one]));
qed "lemma_nth_realpow_non_empty";

Goal "[| (0::real) < a; 0 < n |] \
\     ==> EX u. isUb (UNIV::real set) {x. x ^ n <= a & 0 < x} u";
by (case_tac "1 <= a" 1);
by (res_inst_tac [("x","a")] exI 1);
by (dtac not_real_leE 2);
by (res_inst_tac [("x","1")] exI 2);
by (ALLGOALS(rtac (setleI RS isUbI)));
by Safe_tac;
by (ALLGOALS Simp_tac);
by (ALLGOALS(rtac ccontr));
by (ALLGOALS(dtac not_real_leE));
by (dtac realpow_ge_self2 1 THEN assume_tac 1);
by (dres_inst_tac [("n","n")] realpow_less 1);
by (REPEAT(assume_tac 1));
by (dtac real_le_trans 1 THEN assume_tac 1);
by (dres_inst_tac [("y","y ^ n")] order_less_le_trans 1);
by (assume_tac 1 THEN etac real_less_irrefl 1);
by (dres_inst_tac [("n","n")] ((real_zero_less_one) RS realpow_less) 1);
by (Auto_tac);
qed "lemma_nth_realpow_isUb_ex";

Goal "[| (0::real) < a; 0 < n |] \
\    ==> EX u. isLub (UNIV::real set) {x. x ^ n <= a & 0 < x} u";
by (blast_tac (claset() addIs [lemma_nth_realpow_isUb_ex,
    lemma_nth_realpow_non_empty,reals_complete]) 1);
qed "nth_realpow_isLub_ex";
 
(*---------------------------------------------
          First Half -- lemmas first
 --------------------------------------------*)
Goal "isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u \
\          ==> u + inverse(real_of_posnat k) ~: {x. x ^ n <= a & 0 < x}";
by (Step_tac 1 THEN dtac isLubD2 1 THEN Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_le_def]) 1);
val lemma_nth_realpow_seq = result();

Goal "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u; \
\        0 < a; 0 < n |] ==> 0 < u";
by (dtac lemma_nth_realpow_non_empty 1 THEN Auto_tac);
by (dres_inst_tac [("y","s")] (isLub_isUb RS isUbD) 1);
by (auto_tac (claset() addIs [order_less_le_trans],simpset()));
val lemma_nth_realpow_isLub_gt_zero = result();

Goal "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u; \
\        0 < a; 0 < n |] ==> ALL k. a <= (u + inverse(real_of_posnat k)) ^ n";
by (Step_tac 1);
by (ftac lemma_nth_realpow_seq 1 THEN Step_tac 1);
by (auto_tac (claset() addEs [real_less_asym],
    simpset() addsimps [real_le_def]));
by (fold_tac [real_le_def]);
by (rtac real_less_trans 1);
by (auto_tac (claset() addIs [real_inv_real_of_posnat_gt_zero,
    lemma_nth_realpow_isLub_gt_zero],simpset()));
val lemma_nth_realpow_isLub_ge = result();

(*-----------------------
   First result we want
 ----------------------*)
Goal "[| (0::real) < a; 0 < n; \
\    isLub (UNIV::real set) \
\    {x. x ^ n <= a & 0 < x} u |] ==> a <= u ^ n";
by (ftac lemma_nth_realpow_isLub_ge 1 THEN Step_tac 1);
by (rtac (LIMSEQ_inverse_real_of_posnat_add RS LIMSEQ_pow 
    RS LIMSEQ_le_const) 1);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_def,
    real_of_posnat_Suc]));
qed "realpow_nth_ge";

(*---------------------------------------------
          Second Half
 --------------------------------------------*)

Goal "[| isLub (UNIV::real set) S u; x < u |] \
\          ==> ~ isUb (UNIV::real set) S x";
by (Step_tac 1);
by (dtac isLub_le_isUb 1);
by (assume_tac 1);
by (dtac order_less_le_trans 1);
by (auto_tac (claset(),simpset() 
   addsimps [real_less_not_refl]));
qed "less_isLub_not_isUb";

Goal "~ isUb (UNIV::real set) S u \
\              ==> EX x: S. u < x";
by (rtac ccontr 1 THEN etac swap 1);
by (rtac (setleI RS isUbI) 1);
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
qed "not_isUb_less_ex";

Goal "[| isLub (UNIV::real set) {x. x ^ n <= a & (0::real) < x} u; \
\      0 < a; 0 < n |] ==> ALL k. (u*(1 + -inverse(real_of_posnat k))) ^ n <= a";
by (Step_tac 1);
by (forward_tac [less_isLub_not_isUb RS not_isUb_less_ex] 1);
by (res_inst_tac [("n","k")] real_mult_less_self 1);
by (blast_tac (claset() addIs [lemma_nth_realpow_isLub_gt_zero]) 1);
by (Step_tac 1);
by (dres_inst_tac [("n","k")] (lemma_nth_realpow_isLub_gt_zero RS 
          real_mult_add_one_minus_ge_zero) 1);
by (dtac (conjI RS realpow_le2) 3);
by (rtac (CLAIM "x < y ==> (x::real) <= y") 3);
by (auto_tac (claset() addIs [real_le_trans],simpset()));
val lemma_nth_realpow_isLub_le = result();

(*-----------------------
   Second result we want
 ----------------------*)
Goal "[| (0::real) < a; 0 < n; \
\    isLub (UNIV::real set) \
\    {x. x ^ n <= a & 0 < x} u |] ==> u ^ n <= a";
by (ftac lemma_nth_realpow_isLub_le 1 THEN Step_tac 1);
by (rtac (LIMSEQ_inverse_real_of_posnat_add_minus_mult RS LIMSEQ_pow 
    RS LIMSEQ_le_const2) 1);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_def,real_of_posnat_Suc]));
qed "realpow_nth_le";

(*----------- The theorem at last! -----------*)
Goal "[| (0::real) < a; 0 < n |] ==> EX r. r ^ n = a";
by (ftac nth_realpow_isLub_ex 1 THEN Auto_tac);
by (auto_tac (claset() addIs [realpow_nth_le,
    realpow_nth_ge,real_le_anti_sym],simpset()));
qed "realpow_nth";

(* positive only *)
Goal "[| (0::real) < a; 0 < n |] ==> EX r. 0 < r & r ^ n = a";
by (ftac nth_realpow_isLub_ex 1 THEN Auto_tac);
by (auto_tac (claset() addIs [realpow_nth_le,
    realpow_nth_ge,real_le_anti_sym,
    lemma_nth_realpow_isLub_gt_zero],simpset()));
qed "realpow_pos_nth";

Goal "(0::real) < a  ==> EX r. 0 < r & r ^ Suc n = a";
by (blast_tac (claset() addIs [realpow_pos_nth]) 1);
qed "realpow_pos_nth2";

(* uniqueness of nth positive root *)
Goal "[| (0::real) < a; 0 < n |] ==> EX! r. 0 < r & r ^ n = a";
by (auto_tac (claset() addSIs [realpow_pos_nth],simpset()));
by (cut_inst_tac [("x","r"),("y","y")] linorder_less_linear 1);
by (Auto_tac);
by (dres_inst_tac [("x","r")] realpow_less 1);
by (dres_inst_tac [("x","y")] realpow_less 4);
by (auto_tac (claset(),simpset() addsimps [real_less_not_refl]));
qed "realpow_pos_nth_unique";

