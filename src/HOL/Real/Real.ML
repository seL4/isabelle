(*  Title:      HOL/Real/Real.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "real" is a linear order
*)



(** lemma **)
Goal "(0r < x) = (? y. x = %#y)";
by (auto_tac (claset(),simpset() addsimps [real_preal_zero_less]));
by (cut_inst_tac [("x","x")] real_preal_trichotomy 1);
by (blast_tac (claset() addSEs [real_less_irrefl,
     real_preal_not_minus_gt_zero RS notE]) 1);
qed "real_gt_zero_preal_Ex";

Goal "%#z < x ==> ? y. x = %#y";
by (blast_tac (claset() addSDs [real_preal_zero_less RS real_less_trans]
               addIs [real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_gt_preal_preal_Ex";

Goal "%#z <= x ==> ? y. x = %#y";
by (blast_tac (claset() addDs [real_le_imp_less_or_eq,
              real_gt_preal_preal_Ex]) 1);
qed "real_ge_preal_preal_Ex";

Goal "y <= 0r ==> !x. y < %#x";
by (auto_tac (claset() addEs [real_le_imp_less_or_eq RS disjE]
              addIs [real_preal_zero_less RSN(2,real_less_trans)],
              simpset() addsimps [real_preal_zero_less]));
qed "real_less_all_preal";

Goal "~ 0r < y ==> !x. y < %#x";
by (blast_tac (claset() addSIs [real_less_all_preal,real_leI]) 1);
qed "real_less_all_real2";

Goal "((x::real) < y) = (-y < -x)";
by (rtac (real_less_sum_gt_0_iff RS subst) 1);
by (res_inst_tac [("W1","x")] (real_less_sum_gt_0_iff RS subst) 1);
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_less_swap_iff";

Goal "[| R + L = S; 0r < L |] ==> R < S";
by (rtac (real_less_sum_gt_0_iff RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps real_add_ac));
qed "real_lemma_add_positive_imp_less";

Goal "!!(R::real). ? T. 0r < T & R + T = S ==> R < S";
by (blast_tac (claset() addIs [real_lemma_add_positive_imp_less]) 1);
qed "real_ex_add_positive_left_less";

(*Alternative definition for real_less.  NOT for rewriting*)
Goal "!!(R::real). (R < S) = (? T. 0r < T & R + T = S)";
by (blast_tac (claset() addSIs [real_less_add_positive_left_Ex,
				real_ex_add_positive_left_less]) 1);
qed "real_less_iff_add";

Goal "(0r < x) = (-x < x)";
by Safe_tac;
by (rtac ccontr 2 THEN forward_tac 
    [real_leI RS real_le_imp_less_or_eq] 2);
by (Step_tac 2);
by (dtac (real_minus_zero_less_iff RS iffD2) 2);
by (blast_tac (claset() addIs [real_less_trans]) 2);
by (auto_tac (claset(),
	      simpset() addsimps 
	      [real_gt_zero_preal_Ex,real_preal_minus_less_self]));
qed "real_gt_zero_iff";

Goal "(x < 0r) = (x < -x)";
by (rtac (real_minus_zero_less_iff RS subst) 1);
by (stac real_gt_zero_iff 1);
by (Full_simp_tac 1);
qed "real_lt_zero_iff";

Goalw [real_le_def] "(0r <= x) = (-x <= x)";
by (auto_tac (claset(),simpset() addsimps [real_lt_zero_iff RS sym]));
qed "real_ge_zero_iff";

Goalw [real_le_def] "(x <= 0r) = (x <= -x)";
by (auto_tac (claset(),simpset() addsimps [real_gt_zero_iff RS sym]));
qed "real_le_zero_iff";

Goal "(%#m1 <= %#m2) = (m1 <= m2)";
by (auto_tac (claset() addSIs [preal_leI],
    simpset() addsimps [real_less_le_iff RS sym]));
by (dtac preal_le_less_trans 1 THEN assume_tac 1);
by (etac preal_less_irrefl 1);
qed "real_preal_le_iff";

Goal "!!(x::real). [| 0r < x; 0r < y |] ==> 0r < x * y";
by (auto_tac (claset(),simpset() addsimps [real_gt_zero_preal_Ex]));  
by (res_inst_tac [("x","y*ya")] exI 1);
by (full_simp_tac (simpset() addsimps [real_preal_mult]) 1);
qed "real_mult_order";

Goal "!!(x::real). [| x < 0r; y < 0r |] ==> 0r < x * y";
by (REPEAT(dtac (real_minus_zero_less_iff RS iffD2) 1));
by (dtac real_mult_order 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "real_mult_less_zero1";

Goal "!!(x::real). [| 0r <= x; 0r <= y |] ==> 0r <= x * y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_mult_order, real_less_imp_le],
	      simpset()));
qed "real_le_mult_order";

Goal "!!(x::real). [| x <= 0r; y <= 0r |] ==> 0r <= x * y";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [real_mult_less_zero1],simpset()));
qed "real_mult_le_zero1";

Goal "!!(x::real). [| 0r <= x; y < 0r |] ==> x * y <= 0r";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS subst) 1);
by (blast_tac (claset() addDs [real_mult_order] 
    addIs [real_minus_mult_eq2 RS ssubst]) 1);
qed "real_mult_le_zero";

Goal "!!(x::real). [| 0r < x; y < 0r |] ==> x*y < 0r";
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_mult_eq2]) 1);
qed "real_mult_less_zero";

Goalw [real_one_def] "0r < 1r";
by (auto_tac (claset() addIs [real_gt_zero_preal_Ex RS iffD2],
    simpset() addsimps [real_preal_def]));
qed "real_zero_less_one";

(*** Completeness of reals ***)
(** use supremum property of preal and theorems about real_preal **)
              (*** a few lemmas ***)
Goal "! x:P. 0r < x ==> ((? x:P. y < x) = (? X. %#X : P & y < %#X))";
by (blast_tac (claset() addSDs [bspec,real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_sup_lemma1";

Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? X. X: {w. %#w : P}) & (? Y. !X: {w. %#w : P}. X < Y)";
by (rtac conjI 1);
by (blast_tac (claset() addDs [bspec,real_gt_zero_preal_Ex RS iffD1]) 1);
by Auto_tac;
by (dtac bspec 1 THEN assume_tac 1);
by (forward_tac [bspec] 1  THEN assume_tac 1);
by (dtac real_less_trans 1 THEN assume_tac 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1 THEN etac exE 1);
by (res_inst_tac [("x","ya")] exI 1);
by Auto_tac;
by (dres_inst_tac [("x","%#X")] bspec 1 THEN assume_tac 1);
by (etac real_preal_lessD 1);
qed "real_sup_lemma2";

(*-------------------------------------------------------------
            Completeness of Positive Reals
 -------------------------------------------------------------*)

(* Supremum property for the set of positive reals *)
(* FIXME: long proof - can be improved - need only have one case split *)
(* will do for now *)
Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? S. !y. (? x: P. y < x) = (y < S))";
by (res_inst_tac [("x","%#psup({w. %#w : P})")] exI 1);
by Auto_tac;
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (case_tac "0r < ya" 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (dtac real_less_all_real2 2);
by Auto_tac;
by (rtac (preal_complete RS spec RS iffD1) 1);
by Auto_tac;
by (forward_tac [real_gt_preal_preal_Ex] 1);
by Auto_tac;
(* second part *)
by (rtac (real_sup_lemma1 RS iffD2) 1 THEN assume_tac 1);
by (case_tac "0r < ya" 1);
by (auto_tac (claset() addSDs [real_less_all_real2,
        real_gt_zero_preal_Ex RS iffD1],simpset()));
by (forward_tac [real_sup_lemma2] 2 THEN Auto_tac);
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (rtac (preal_complete RS spec RS iffD2 RS bexE) 1);
by (Blast_tac 3);
by (Blast_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "posreal_complete";



(*** Monotonicity results ***)

Goal "(v+z < w+z) = (v < (w::real))";
by (Simp_tac 1);
qed "real_add_right_cancel_less";

Goal "(z+v < z+w) = (v < (w::real))";
by (Simp_tac 1);
qed "real_add_left_cancel_less";

Addsimps [real_add_right_cancel_less, real_add_left_cancel_less];

Goal "(v+z <= w+z) = (v <= (w::real))";
by (Simp_tac 1);
qed "real_add_right_cancel_le";

Goal "(z+v <= z+w) = (v <= (w::real))";
by (Simp_tac 1);
qed "real_add_left_cancel_le";

Addsimps [real_add_right_cancel_le, real_add_left_cancel_le];

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("real_add_less_mono1", real_add_right_cancel_less RS iffD2);

(*"v<=w ==> v+z <= w+z"*)
bind_thm ("real_add_le_mono1", real_add_right_cancel_le RS iffD2);

Goal "!!z z'::real. [| w'<w; z'<=z |] ==> w' + z' < w + z";
by (etac (real_add_less_mono1 RS real_less_le_trans) 1);
by (Simp_tac 1);
qed "real_add_less_mono";


Goal "!!(A::real). A < B ==> C + A < C + B";
by (Simp_tac 1);
qed "real_add_less_mono2";

Goal "!!(A::real). A + C < B + C ==> A < B";
by (Full_simp_tac 1);
qed "real_less_add_right_cancel";

Goal "!!(A::real). C + A < C + B ==> A < B";
by (Full_simp_tac 1);
qed "real_less_add_left_cancel";

Goal "[| 0r < x; 0r < y |] ==> 0r < x + y";
by (etac real_less_trans 1);
by (dtac real_add_less_mono2 1);
by (Full_simp_tac 1);
qed "real_add_order";

Goal "!!(x::real). [| 0r <= x; 0r <= y |] ==> 0r <= x + y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_add_order, real_less_imp_le],
	      simpset()));
qed "real_le_add_order";

Goal "[| R1 < S1; R2 < S2 |] ==> R1 + R2 < S1 + (S2::real)";
by (dtac real_add_less_mono1 1);
by (etac real_less_trans 1);
by (etac real_add_less_mono2 1);
qed "real_add_less_mono";

Goal "!!(q1::real). q1 <= q2  ==> x + q1 <= x + q2";
by (Simp_tac 1);
qed "real_add_left_le_mono1";

Goal "[|i<=j;  k<=l |] ==> i + k <= j + (l::real)";
by (dtac real_add_le_mono1 1);
by (etac real_le_trans 1);
by (Simp_tac 1);
qed "real_add_le_mono";

Goal "EX (x::real). x < y";
by (rtac (real_add_zero_right RS subst) 1);
by (res_inst_tac [("x","y + -1r")] exI 1);
by (auto_tac (claset() addSIs [real_add_less_mono2],
	  simpset() addsimps [real_minus_zero_less_iff2, real_zero_less_one]));
qed "real_less_Ex";

(*---------------------------------------------------------------------------------
             An embedding of the naturals in the reals
 ---------------------------------------------------------------------------------*)

Goalw [real_nat_def] "%%#0 = 1r";
by (full_simp_tac (simpset() addsimps [pnat_one_iff RS sym,real_preal_def]) 1);
by (fold_tac [real_one_def]);
by (rtac refl 1);
qed "real_nat_one";

Goalw [real_nat_def] "%%#1 = 1r + 1r";
by (full_simp_tac (simpset() addsimps [real_preal_def,real_one_def,
    pnat_two_eq,real_add,prat_pnat_add RS sym,preal_prat_add RS sym
    ] @ pnat_add_ac) 1);
qed "real_nat_two";

Goalw [real_nat_def]
          "%%#n1 + %%#n2 = %%#(n1 + n2) + 1r";
by (full_simp_tac (simpset() addsimps [real_nat_one RS sym,
    real_nat_def,real_preal_add RS sym,preal_prat_add RS sym,
    prat_pnat_add RS sym,pnat_nat_add]) 1);
qed "real_nat_add";

Goal "%%#(n + 1) = %%#n + 1r";
by (res_inst_tac [("x1","1r")] (real_add_right_cancel RS iffD1) 1);
by (rtac (real_nat_add RS subst) 1);
by (full_simp_tac (simpset() addsimps [real_nat_two,real_add_assoc]) 1);
qed "real_nat_add_one";

Goal "Suc n = n + 1";
by Auto_tac;
qed "lemma";

Goal "%%#Suc n = %%#n + 1r";
by (stac lemma 1);
by (rtac real_nat_add_one 1);
qed "real_nat_Suc";

Goal "inj(real_nat)";
by (rtac injI 1);
by (rewtac real_nat_def);
by (dtac (inj_real_preal RS injD) 1);
by (dtac (inj_preal_prat RS injD) 1);
by (dtac (inj_prat_pnat RS injD) 1);
by (etac (inj_pnat_nat RS injD) 1);
qed "inj_real_nat";

Goalw [real_nat_def] "0r < %%#n";
by (rtac (real_gt_zero_preal_Ex RS iffD2) 1);
by (Blast_tac 1);
qed "real_nat_less_zero";

Goal "1r <= %%#n";
by (simp_tac (simpset() addsimps [real_nat_one RS sym]) 1);
by (induct_tac "n" 1);
by (auto_tac (claset(),
	      simpset () addsimps [real_nat_Suc,real_nat_one,
				   real_nat_less_zero, real_less_imp_le]));
qed "real_nat_less_one";

Goal "rinv(%%#n) ~= 0r";
by (rtac ((real_nat_less_zero RS 
    real_not_refl2 RS not_sym) RS rinv_not_zero) 1);
qed "real_nat_rinv_not_zero";

Goal "rinv(%%#x) = rinv(%%#y) ==> x = y";
by (rtac (inj_real_nat RS injD) 1);
by (res_inst_tac [("n2","x")] 
    (real_nat_rinv_not_zero RS real_mult_left_cancel RS iffD1) 1);
by (full_simp_tac (simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym) RS real_mult_inv_left]) 1);
by (asm_full_simp_tac (simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym)]) 1);
qed "real_nat_rinv_inj";

Goal "0r < x ==> 0r < rinv x";
by (EVERY1[rtac ccontr, dtac real_leI]);
by (forward_tac [real_minus_zero_less_iff2 RS iffD2] 1);
by (forward_tac [real_not_refl2 RS not_sym] 1);
by (dtac (real_not_refl2 RS not_sym RS rinv_not_zero) 1);
by (EVERY1[dtac real_le_imp_less_or_eq, Step_tac]); 
by (dtac real_mult_less_zero1 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [real_zero_less_one RS real_less_asym],
    simpset() addsimps [real_minus_mult_eq1 RS sym]));
qed "real_rinv_gt_zero";

Goal "x < 0r ==> rinv x < 0r";
by (forward_tac [real_not_refl2] 1);
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (dtac (real_minus_rinv RS sym) 1);
by (auto_tac (claset() addIs [real_rinv_gt_zero],
    simpset()));
qed "real_rinv_less_zero";

Goal "x+x=x*(1r+1r)";
by (simp_tac (simpset() addsimps [real_add_mult_distrib2]) 1);
qed "real_add_self";

Goal "x < x + 1r";
by (rtac (real_less_sum_gt_0_iff RS iffD1) 1);
by (full_simp_tac (simpset() addsimps [real_zero_less_one,
				real_add_assoc, real_add_left_commute]) 1);
qed "real_self_less_add_one";

Goal "1r < 1r + 1r";
by (rtac real_self_less_add_one 1);
qed "real_one_less_two";

Goal "0r < 1r + 1r";
by (rtac ([real_zero_less_one,
	   real_one_less_two] MRS real_less_trans) 1);
qed "real_zero_less_two";

Goal "1r + 1r ~= 0r";
by (rtac (real_zero_less_two RS real_not_refl2 RS not_sym) 1);
qed "real_two_not_zero";

Addsimps [real_two_not_zero];

Goal "x*rinv(1r + 1r) + x*rinv(1r + 1r) = x";
by (stac real_add_self 1);
by (full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_sum_of_halves";

Goal "!!(x::real). [| 0r<z; x<y |] ==> x*z<y*z";       
by (rotate_tac 1 1);
by (dtac real_less_sum_gt_zero 1);
by (rtac real_sum_gt_zero_less 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_minus_mult_eq2 RS sym, real_mult_commute ]) 1);
qed "real_mult_less_mono1";

Goal "!!(y::real). [| 0r<z; x<y |] ==> z*x<z*y";       
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_less_mono1]) 1);
qed "real_mult_less_mono2";

Goal "!!(x::real). [| 0r<z; x*z<y*z |] ==> x<y";
by (forw_inst_tac [("x","x*z")] (real_rinv_gt_zero 
                       RS real_mult_less_mono1) 1);
by (auto_tac (claset(),
	      simpset() addsimps 
     [real_mult_assoc,real_not_refl2 RS not_sym]));
qed "real_mult_less_cancel1";

Goal "!!(x::real). [| 0r<z; z*x<z*y |] ==> x<y";
by (etac real_mult_less_cancel1 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "real_mult_less_cancel2";

Goal "0r < z ==> (x*z < y*z) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono1,
    real_mult_less_cancel1]) 1);
qed "real_mult_less_iff1";

Goal "0r < z ==> (z*x < z*y) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono2,
    real_mult_less_cancel2]) 1);
qed "real_mult_less_iff2";

Addsimps [real_mult_less_iff1,real_mult_less_iff2];

Goal "!!(x::real). [| 0r<=z; x<y |] ==> x*z<=y*z";
by (EVERY1 [rtac real_less_or_eq_imp_le, dtac real_le_imp_less_or_eq]);
by (auto_tac (claset() addIs [real_mult_less_mono1],simpset()));
qed "real_mult_le_less_mono1";

Goal "!!(x::real). [| 0r<=z; x<y |] ==> z*x<=z*y";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_le_less_mono1]) 1);
qed "real_mult_le_less_mono2";

Goal "!!x y (z::real). [| 0r<=z; x<=y |] ==> z*x<=z*y";
by (dres_inst_tac [("x","x")] real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_less_mono2], simpset()));
qed "real_mult_le_le_mono1";

Goal "!!(x::real). x < y ==> x < (x + y)*rinv(1r + 1r)";
by (dres_inst_tac [("C","x")] real_add_less_mono2 1);
by (dtac (real_add_self RS subst) 1);
by (dtac (real_zero_less_two RS real_rinv_gt_zero RS 
          real_mult_less_mono1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_less_half_sum";

Goal "!!(x::real). x < y ==> (x + y)*rinv(1r + 1r) < y";
by (dtac real_add_less_mono1 1);
by (dtac (real_add_self RS subst) 1);
by (dtac (real_zero_less_two RS real_rinv_gt_zero RS 
          real_mult_less_mono1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_gt_half_sum";

Goal "!!(x::real). x < y ==> EX r. x < r & r < y";
by (blast_tac (claset() addSIs [real_less_half_sum,real_gt_half_sum]) 1);
qed "real_dense";

Goal "(EX n. rinv(%%#n) < r) = (EX n. 1r < r * %%#n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_nat_less_zero 
                       RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_nat_less_zero RS 
        real_rinv_gt_zero RS real_mult_less_mono1) 2);
by (auto_tac (claset(),
	      simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym),real_mult_assoc]));
qed "real_nat_rinv_Ex_iff";

Goalw [real_nat_def] "(%%#n < %%#m) = (n < m)";
by Auto_tac;
qed "real_nat_less_iff";

Addsimps [real_nat_less_iff];

Goal "0r < u  ==> (u < rinv (%%#n)) = (%%#n < rinv(u))";
by (Step_tac 1);
by (res_inst_tac [("n2","n")] (real_nat_less_zero RS 
    real_rinv_gt_zero RS real_mult_less_cancel1) 1);
by (res_inst_tac [("x1","u")] ( real_rinv_gt_zero
   RS real_mult_less_cancel1) 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_nat_less_zero, 
    real_not_refl2 RS not_sym]));
by (res_inst_tac [("z","u")] real_mult_less_cancel2 1);
by (res_inst_tac [("n1","n")] (real_nat_less_zero RS 
    real_mult_less_cancel2) 3);
by (auto_tac (claset(),
	      simpset() addsimps [real_nat_less_zero, 
    real_not_refl2 RS not_sym,real_mult_assoc RS sym]));
qed "real_nat_less_rinv_iff";

Goal "0r < u ==> (u = rinv(%%#n)) = (%%#n = rinv u)";
by (auto_tac (claset(),
	      simpset() addsimps [real_rinv_rinv,
    real_nat_less_zero,real_not_refl2 RS not_sym]));
qed "real_nat_rinv_eq_iff";

(*
(*------------------------------------------------------------------
     lemmas about upper bounds and least upper bound
 ------------------------------------------------------------------*)
Goalw [real_ub_def] "[| real_ub u S; x : S |] ==> x <= u";
by Auto_tac;
qed "real_ubD";

*)


