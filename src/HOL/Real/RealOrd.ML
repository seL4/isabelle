(*  Title:       HOL/Real/Real.ML
    ID:          $Id$
    Author:      Jacques D. Fleuriot and Lawrence C. Paulson
    Copyright:   1998  University of Cambridge
    Description: Type "real" is a linear order
*)

(**** The simproc abel_cancel ****)

(*** Two lemmas needed for the simprocs ***)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::real) + (y + z) = y + u) = ((x + z) = u)";
by (stac real_add_left_commute 1);
by (rtac real_add_left_cancel 1);
qed "real_add_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::real) + (y + z) = y) = (x = -z)";
by (stac real_add_left_commute 1);
by (res_inst_tac [("t", "y")] (real_add_zero_right RS subst) 1
    THEN stac real_add_left_cancel 1);
by (simp_tac (simpset() addsimps [real_eq_diff_eq RS sym]) 1);
qed "real_add_cancel_end";


structure Real_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref		= Sign.self_ref (Theory.sign_of (the_context ()))
  val T			= HOLogic.realT
  val zero		= Const ("0", T)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= real_add_cancel_21
  val add_cancel_end	= real_add_cancel_end
  val add_left_cancel	= real_add_left_cancel
  val add_assoc		= real_add_assoc
  val add_commute	= real_add_commute
  val add_left_commute	= real_add_left_commute
  val add_0		= real_add_zero_left
  val add_0_right	= real_add_zero_right

  val eq_diff_eq	= real_eq_diff_eq
  val eqI_rules		= [real_less_eqI, real_eq_eqI, real_le_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= real_diff_def
  val minus_add_distrib	= real_minus_add_distrib
  val minus_minus	= real_minus_minus
  val minus_0		= real_minus_zero
  val add_inverses	= [real_add_minus, real_add_minus_left]
  val cancel_simps	= [real_add_minus_cancel, real_minus_add_cancel]
end;

structure Real_Cancel = Abel_Cancel (Real_Cancel_Data);

Addsimprocs [Real_Cancel.sum_conv, Real_Cancel.rel_conv];

Goal "- (z - y) = y - (z::real)";
by (Simp_tac 1);
qed "real_minus_diff_eq";
Addsimps [real_minus_diff_eq];


(**** Theorems about the ordering ****)

Goal "(0 < x) = (EX y. x = real_of_preal y)";
by (auto_tac (claset(), simpset() addsimps [real_of_preal_zero_less]));
by (cut_inst_tac [("x","x")] real_of_preal_trichotomy 1);
by (blast_tac (claset() addSEs [real_less_irrefl,
				real_of_preal_not_minus_gt_zero RS notE]) 1);
qed "real_gt_zero_preal_Ex";

Goal "real_of_preal z < x ==> EX y. x = real_of_preal y";
by (blast_tac (claset() addSDs [real_of_preal_zero_less RS real_less_trans]
               addIs [real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_gt_preal_preal_Ex";

Goal "real_of_preal z <= x ==> EX y. x = real_of_preal y";
by (blast_tac (claset() addDs [real_le_imp_less_or_eq,
			       real_gt_preal_preal_Ex]) 1);
qed "real_ge_preal_preal_Ex";

Goal "y <= 0 ==> ALL x. y < real_of_preal x";
by (auto_tac (claset() addEs [real_le_imp_less_or_eq RS disjE]
                       addIs [real_of_preal_zero_less RSN(2,real_less_trans)],
              simpset() addsimps [real_of_preal_zero_less]));
qed "real_less_all_preal";

Goal "~ 0 < y ==> ALL x. y < real_of_preal x";
by (blast_tac (claset() addSIs [real_less_all_preal,real_leI]) 1);
qed "real_less_all_real2";

Goal "[| R + L = S;  (0::real) < L |] ==> R < S";
by (rtac (real_less_sum_gt_0_iff RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps real_add_ac));
qed "real_lemma_add_positive_imp_less";

Goal "EX T::real. 0 < T & R + T = S ==> R < S";
by (blast_tac (claset() addIs [real_lemma_add_positive_imp_less]) 1);
qed "real_ex_add_positive_left_less";

(*Alternative definition for real_less.  NOT for rewriting*)
Goal "(R < S) = (EX T::real. 0 < T & R + T = S)";
by (blast_tac (claset() addSIs [real_less_add_positive_left_Ex,
				real_ex_add_positive_left_less]) 1);
qed "real_less_iff_add";

Goal "(real_of_preal m1 <= real_of_preal m2) = (m1 <= m2)";
by (auto_tac (claset() addSIs [preal_leI],
    simpset() addsimps [real_less_le_iff RS sym]));
by (dtac preal_le_less_trans 1 THEN assume_tac 1);
by (etac preal_less_irrefl 1);
qed "real_of_preal_le_iff";

Goal "[| 0 < x; 0 < y |] ==> (0::real) < x * y";
by (auto_tac (claset(), simpset() addsimps [real_gt_zero_preal_Ex]));  
by (res_inst_tac [("x","y*ya")] exI 1);
by (full_simp_tac (simpset() addsimps [real_of_preal_mult]) 1);
qed "real_mult_order";

Goal "[| x < 0; y < 0 |] ==> (0::real) < x * y";
by (REPEAT(dtac (real_minus_zero_less_iff RS iffD2) 1));
by (dtac real_mult_order 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "real_mult_less_zero1";

Goal "[| 0 <= x; 0 <= y |] ==> (0::real) <= x * y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_mult_order, real_less_imp_le],
	      simpset()));
qed "real_le_mult_order";

Goal "[| 0 < x; 0 <= y |] ==> (0::real) <= x * y";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_order,
			      real_less_imp_le],simpset()));
qed "real_less_le_mult_order";

Goal "[| x <= 0; y <= 0 |] ==> (0::real) <= x * y";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [real_mult_less_zero1],simpset()));
qed "real_mult_le_zero1";

Goal "[| 0 <= x; y < 0 |] ==> x * y <= (0::real)";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS subst) 1);
by (blast_tac (claset() addDs [real_mult_order] 
	                addIs [real_minus_mult_eq2 RS ssubst]) 1);
qed "real_mult_le_zero";

Goal "[| 0 < x; y < 0 |] ==> x*y < (0::real)";
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (Asm_full_simp_tac 1);
qed "real_mult_less_zero";

Goalw [real_one_def] "0 < 1r";
by (auto_tac (claset() addIs [real_gt_zero_preal_Ex RS iffD2],
	      simpset() addsimps [real_of_preal_def]));
qed "real_zero_less_one";

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
qed "real_add_less_le_mono";

Goal "!!z z'::real. [| w'<=w; z'<z |] ==> w' + z' < w + z";
by (etac (real_add_le_mono1 RS real_le_less_trans) 1);
by (Simp_tac 1);
qed "real_add_le_less_mono";

Goal "!!(A::real). A < B ==> C + A < C + B";
by (Simp_tac 1);
qed "real_add_less_mono2";

Goal "!!(A::real). A + C < B + C ==> A < B";
by (Full_simp_tac 1);
qed "real_less_add_right_cancel";

Goal "!!(A::real). C + A < C + B ==> A < B";
by (Full_simp_tac 1);
qed "real_less_add_left_cancel";

Goal "!!(A::real). A + C <= B + C ==> A <= B";
by (Full_simp_tac 1);
qed "real_le_add_right_cancel";

Goal "!!(A::real). C + A <= C + B ==> A <= B";
by (Full_simp_tac 1);
qed "real_le_add_left_cancel";

Goal "[| 0 < x; 0 < y |] ==> (0::real) < x + y";
by (etac real_less_trans 1);
by (dtac real_add_less_mono2 1);
by (Full_simp_tac 1);
qed "real_add_order";

Goal "[| 0 <= x; 0 <= y |] ==> (0::real) <= x + y";
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
by (res_inst_tac [("x","y + (-1r)")] exI 1);
by (auto_tac (claset() addSIs [real_add_less_mono2],
	  simpset() addsimps [real_minus_zero_less_iff2, real_zero_less_one]));
qed "real_less_Ex";

Goal "(0::real) < r ==>  u + (-r) < u";
by (res_inst_tac [("C","r")] real_less_add_right_cancel 1);
by (simp_tac (simpset() addsimps [real_add_assoc]) 1);
qed "real_add_minus_positive_less_self";

Goal "(-s <= -r) = ((r::real) <= s)";
by (rtac sym 1);
by (Step_tac 1);
by (dres_inst_tac [("x","-s")] real_add_left_le_mono1 1);
by (dres_inst_tac [("x","r")] real_add_left_le_mono1 2);
by Auto_tac;
by (dres_inst_tac [("z","-r")] real_add_le_mono1 1);
by (dres_inst_tac [("z","s")] real_add_le_mono1 2);
by (auto_tac (claset(), simpset() addsimps [real_add_assoc]));
qed "real_le_minus_iff";
Addsimps [real_le_minus_iff];
          
Goal "0 <= 1r";
by (rtac (real_zero_less_one RS real_less_imp_le) 1);
qed "real_zero_le_one";
Addsimps [real_zero_le_one];

Goal "(0::real) <= x*x";
by (res_inst_tac [("R2.0","0"),("R1.0","x")] real_linear_less2 1);
by (auto_tac (claset() addIs [real_mult_order,
			      real_mult_less_zero1,real_less_imp_le],
	      simpset()));
qed "real_le_square";
Addsimps [real_le_square];

(*----------------------------------------------------------------------------
             An embedding of the naturals in the reals
 ----------------------------------------------------------------------------*)

Goalw [real_of_posnat_def] "real_of_posnat 0 = 1r";
by (full_simp_tac (simpset() addsimps [pnat_one_iff RS sym,real_of_preal_def]) 1);
by (fold_tac [real_one_def]);
by (rtac refl 1);
qed "real_of_posnat_one";

Goalw [real_of_posnat_def] "real_of_posnat 1 = 1r + 1r";
by (full_simp_tac (simpset() addsimps [real_of_preal_def,real_one_def,
    pnat_two_eq,real_add,prat_of_pnat_add RS sym,preal_of_prat_add RS sym
    ] @ pnat_add_ac) 1);
qed "real_of_posnat_two";

Goalw [real_of_posnat_def]
    "real_of_posnat n1 + real_of_posnat n2 = real_of_posnat (n1 + n2) + 1r";
by (full_simp_tac (simpset() addsimps [real_of_posnat_one RS sym,
    real_of_posnat_def,real_of_preal_add RS sym,preal_of_prat_add RS sym,
    prat_of_pnat_add RS sym,pnat_of_nat_add]) 1);
qed "real_of_posnat_add";

Goal "real_of_posnat (n + 1) = real_of_posnat n + 1r";
by (res_inst_tac [("x1","1r")] (real_add_right_cancel RS iffD1) 1);
by (rtac (real_of_posnat_add RS subst) 1);
by (full_simp_tac (simpset() addsimps [real_of_posnat_two,real_add_assoc]) 1);
qed "real_of_posnat_add_one";

Goal "real_of_posnat (Suc n) = real_of_posnat n + 1r";
by (stac (real_of_posnat_add_one RS sym) 1);
by (Simp_tac 1);
qed "real_of_posnat_Suc";

Goal "inj(real_of_posnat)";
by (rtac injI 1);
by (rewtac real_of_posnat_def);
by (dtac (inj_real_of_preal RS injD) 1);
by (dtac (inj_preal_of_prat RS injD) 1);
by (dtac (inj_prat_of_pnat RS injD) 1);
by (etac (inj_pnat_of_nat RS injD) 1);
qed "inj_real_of_posnat";

Goalw [real_of_posnat_def] "0 < real_of_posnat n";
by (rtac (real_gt_zero_preal_Ex RS iffD2) 1);
by (Blast_tac 1);
qed "real_of_posnat_gt_zero";

Goal "real_of_posnat n ~= 0";
by (rtac (real_of_posnat_gt_zero RS real_not_refl2 RS not_sym) 1);
qed "real_of_posnat_not_eq_zero";
Addsimps[real_of_posnat_not_eq_zero];

Goal "1r <= real_of_posnat n";
by (simp_tac (simpset() addsimps [real_of_posnat_one RS sym]) 1);
by (induct_tac "n" 1);
by (auto_tac (claset(),
	      simpset () addsimps [real_of_posnat_Suc,real_of_posnat_one,
			   real_of_posnat_gt_zero, real_less_imp_le]));
qed "real_of_posnat_less_one";
Addsimps [real_of_posnat_less_one];

Goal "inverse (real_of_posnat n) ~= 0";
by (rtac ((real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym) RS real_inverse_not_zero) 1);
qed "real_of_posnat_inverse_not_zero";
Addsimps [real_of_posnat_inverse_not_zero];

Goal "inverse (real_of_posnat x) = inverse (real_of_posnat y) ==> x = y";
by (rtac (inj_real_of_posnat RS injD) 1);
by (res_inst_tac [("n2","x")] 
    (real_of_posnat_inverse_not_zero RS real_mult_left_cancel RS iffD1) 1);
by (full_simp_tac (simpset() addsimps [(real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym) RS real_mult_inv_left]) 1);
by (asm_full_simp_tac (simpset() addsimps [(real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym)]) 1);
qed "real_of_posnat_inverse_inj";

Goal "0 < x ==> 0 < inverse (x::real)";
by (EVERY1[rtac ccontr, dtac real_leI]);
by (forward_tac [real_minus_zero_less_iff2 RS iffD2] 1);
by (forward_tac [real_not_refl2 RS not_sym] 1);
by (dtac (real_not_refl2 RS not_sym RS real_inverse_not_zero) 1);
by (EVERY1[dtac real_le_imp_less_or_eq, Step_tac]); 
by (dtac real_mult_less_zero1 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [real_zero_less_one RS real_less_asym],
	      simpset()));
qed "real_inverse_gt_zero";

Goal "x < 0 ==> inverse (x::real) < 0";
by (ftac real_not_refl2 1);
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (stac (real_minus_inverse RS sym) 1);
by (auto_tac (claset() addIs [real_inverse_gt_zero], simpset()));
qed "real_inverse_less_zero";

Goal "0 < inverse (real_of_posnat n)";
by (rtac (real_of_posnat_gt_zero RS real_inverse_gt_zero) 1);
qed "real_of_posnat_inverse_gt_zero";
Addsimps [real_of_posnat_inverse_gt_zero];

Goal "real_of_preal (preal_of_prat (prat_of_pnat (pnat_of_nat N))) = \
\     real_of_nat (Suc N)";
by (simp_tac (simpset() addsimps [real_of_nat_def,real_of_posnat_Suc,
    real_add_assoc,(real_of_posnat_def RS meta_eq_to_obj_eq) RS sym]) 1);
qed "real_of_preal_real_of_nat_Suc";

Goal "x+x = x*(1r+1r)";
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

Goal "0 < 1r + 1r";
by (rtac ([real_zero_less_one,
	   real_one_less_two] MRS real_less_trans) 1);
qed "real_zero_less_two";

Goal "1r + 1r ~= 0";
by (rtac (real_zero_less_two RS real_not_refl2 RS not_sym) 1);
qed "real_two_not_zero";

Addsimps [real_two_not_zero];

Goal "x * inverse (1r + 1r) + x * inverse(1r + 1r) = x";
by (stac real_add_self 1);
by (full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_sum_of_halves";

Goal "[| (0::real) < z; x < y |] ==> x*z < y*z";       
by (rotate_tac 1 1);
by (dtac real_less_sum_gt_zero 1);
by (rtac real_sum_gt_zero_less 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
					   real_mult_commute ]) 1);
qed "real_mult_less_mono1";

Goal "[| (0::real) < z; x < y |] ==> z * x < z * y";       
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_less_mono1]) 1);
qed "real_mult_less_mono2";

Goal "[| (0::real) < z; x * z < y * z |] ==> x < y";
by (forw_inst_tac [("x","x*z")] (real_inverse_gt_zero 
                       RS real_mult_less_mono1) 1);
by (auto_tac (claset(),
	      simpset() addsimps 
     [real_mult_assoc,real_not_refl2 RS not_sym]));
qed "real_mult_less_cancel1";

Goal "[| (0::real) < z; z*x < z*y |] ==> x < y";
by (etac real_mult_less_cancel1 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "real_mult_less_cancel2";

Goal "(0::real) < z ==> (x*z < y*z) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono1,
    real_mult_less_cancel1]) 1);
qed "real_mult_less_iff1";

Goal "(0::real) < z ==> (z*x < z*y) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono2,
    real_mult_less_cancel2]) 1);
qed "real_mult_less_iff2";

Addsimps [real_mult_less_iff1,real_mult_less_iff2];

(* 05/00 *)
Goalw [real_le_def] "(0::real) < z ==> (x*z <= y*z) = (x <= y)";
by (Auto_tac);
qed "real_mult_le_cancel_iff1";

Goalw [real_le_def] "(0::real) < z ==> (z*x <= z*y) = (x <= y)";
by (Auto_tac);
qed "real_mult_le_cancel_iff2";

Addsimps [real_mult_le_cancel_iff1,real_mult_le_cancel_iff2];


Goal "[| (0::real) <= z; x < y |] ==> x*z <= y*z";
by (EVERY1 [rtac real_less_or_eq_imp_le, dtac real_le_imp_less_or_eq]);
by (auto_tac (claset() addIs [real_mult_less_mono1],simpset()));
qed "real_mult_le_less_mono1";

Goal "[| (0::real) <= z; x < y |] ==> z*x <= z*y";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_le_less_mono1]) 1);
qed "real_mult_le_less_mono2";

Goal "[| (0::real) <= z; x <= y |] ==> z*x <= z*y";
by (dres_inst_tac [("x","x")] real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_less_mono2], simpset()));
qed "real_mult_le_le_mono1";

Goal "[| (0::real) < r1; r1 < r2; 0 < x; x < y|] ==> r1 * x < r2 * y";
by (dres_inst_tac [("x","x")] real_mult_less_mono2 1);
by (dres_inst_tac [("R1.0","0")] real_less_trans 2);
by (dres_inst_tac [("x","r1")] real_mult_less_mono1 3);
by Auto_tac;
by (blast_tac (claset() addIs [real_less_trans]) 1);
qed "real_mult_less_mono";

Goal "[| (0::real) < r1; r1  < r2;  0 < y|] ==> 0 < r2 * y";
by (rtac real_mult_order 1); 
by (assume_tac 2);
by (blast_tac (claset() addIs [real_less_trans]) 1);
qed "real_mult_order_trans";

Goal "[| (0::real) < r1; r1  < r2;  0 <= x; x < y|] ==> r1 * x < r2 * y";
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq] 
	               addIs [real_mult_less_mono,real_mult_order_trans],
              simpset()));
qed "real_mult_less_mono3";

Goal "[| (0::real) <= r1; r1  < r2;  0 <= x; x < y|] ==> r1 * x < r2 * y";
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq] 
	               addIs [real_mult_less_mono,real_mult_order_trans,
			      real_mult_order],
	      simpset()));
by (dres_inst_tac [("R2.0","x")] real_less_trans 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [real_mult_order]) 1);
qed "real_mult_less_mono4";

Goal "[| (0::real) < r1; r1 <= r2;  0 <= x; x <= y |] ==> r1 * x <= r2 * y";
by (rtac real_less_or_eq_imp_le 1);
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_mult_less_mono,
			      real_mult_order_trans,real_mult_order],
	      simpset()));
qed "real_mult_le_mono";

Goal "[| (0::real) < r1; r1 < r2;  0 <= x; x <= y |] ==> r1 * x <= r2 * y";
by (rtac real_less_or_eq_imp_le 1);
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_mult_less_mono, real_mult_order_trans,
			      real_mult_order],
	      simpset()));
qed "real_mult_le_mono2";

Goal "[| (0::real) <= r1; r1 < r2;  0 <= x; x <= y |] ==> r1 * x <= r2 * y";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_mono2],simpset()));
by (dtac real_le_trans 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [real_less_le_mult_order], simpset()));
qed "real_mult_le_mono3";

Goal "[| (0::real) <= r1; r1 <= r2;  0 <= x; x <= y |] ==> r1 * x <= r2 * y";
by (dres_inst_tac [("x","r1")] real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_mono3, real_mult_le_le_mono1],
	      simpset()));
qed "real_mult_le_mono4";

Goal "1r <= x ==> 0 < x";
by (rtac ccontr 1 THEN dtac real_leI 1);
by (dtac real_le_trans 1 THEN assume_tac 1);
by (auto_tac (claset() addDs [real_zero_less_one RSN (2,real_le_less_trans)],
	      simpset() addsimps [real_less_not_refl]));
qed "real_gt_zero";

Goal "[| 1r < r; 1r <= x |]  ==> x <= r * x";
by (dtac (real_gt_zero RS real_less_imp_le) 1);
by (auto_tac (claset() addSDs [real_mult_le_less_mono1],
    simpset()));
qed "real_mult_self_le";

Goal "[| 1r <= r; 1r <= x |]  ==> x <= r * x";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_self_le],
	      simpset() addsimps [real_le_refl]));
qed "real_mult_self_le2";

Goal "(EX n. inverse (real_of_posnat n) < r) = (EX n. 1r < r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_of_posnat_gt_zero 
				RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
				real_inverse_gt_zero RS real_mult_less_mono1) 2);
by (auto_tac (claset(),
	      simpset() addsimps [(real_of_posnat_gt_zero RS 
				   real_not_refl2 RS not_sym),
				  real_mult_assoc]));
qed "real_of_posnat_inverse_Ex_iff";

Goal "(inverse(real_of_posnat n) < r) = (1r < r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_of_posnat_gt_zero 
                       RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
				real_inverse_gt_zero RS real_mult_less_mono1) 2);
by (auto_tac (claset(), simpset() addsimps [real_mult_assoc]));
qed "real_of_posnat_inverse_iff";

Goal "(inverse (real_of_posnat n) <= r) = (1r <= r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
    real_less_imp_le RS real_mult_le_le_mono1) 1);
by (dres_inst_tac [("n3","n")] (real_of_posnat_gt_zero RS 
        real_inverse_gt_zero RS real_less_imp_le RS 
        real_mult_le_le_mono1) 2);
by (auto_tac (claset(), simpset() addsimps real_mult_ac));
qed "real_of_posnat_inverse_le_iff";

Goalw [real_of_posnat_def] "(real_of_posnat n < real_of_posnat m) = (n < m)";
by Auto_tac;
qed "real_of_posnat_less_iff";

Addsimps [real_of_posnat_less_iff];

Goal "0 < u  ==> (u < inverse (real_of_posnat n)) = (real_of_posnat n < inverse u)";
by (Step_tac 1);
by (res_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
    real_inverse_gt_zero RS real_mult_less_cancel1) 1);
by (res_inst_tac [("x1","u")] ( real_inverse_gt_zero
   RS real_mult_less_cancel1) 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_posnat_gt_zero, 
    real_not_refl2 RS not_sym]));
by (res_inst_tac [("z","u")] real_mult_less_cancel2 1);
by (res_inst_tac [("n1","n")] (real_of_posnat_gt_zero RS 
    real_mult_less_cancel2) 3);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_posnat_gt_zero, 
    real_not_refl2 RS not_sym,real_mult_assoc RS sym]));
qed "real_of_posnat_less_inverse_iff";

Goal "0 < u ==> (u = inverse (real_of_posnat n)) = (real_of_posnat n = inverse u)";
by (auto_tac (claset(),
	      simpset() addsimps [real_inverse_inverse, real_of_posnat_gt_zero, 
				  real_not_refl2 RS not_sym]));
qed "real_of_posnat_inverse_eq_iff";

Goal "[| 0 < r; r < x |] ==> inverse x < inverse (r::real)";
by (ftac real_less_trans 1 THEN assume_tac 1);
by (ftac real_inverse_gt_zero 1);
by (forw_inst_tac [("x","x")] real_inverse_gt_zero 1);
by (forw_inst_tac [("x","r"),("z","inverse r")] real_mult_less_mono1 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_not_refl2 RS 
					   not_sym RS real_mult_inv_right]) 1);
by (ftac real_inverse_gt_zero 1);
by (forw_inst_tac [("x","1r"),("z","inverse x")] real_mult_less_mono2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_not_refl2 RS 
         not_sym RS real_mult_inv_left,real_mult_assoc RS sym]) 1);
qed "real_inverse_less_swap";

Goal "r < r + inverse (real_of_posnat n)";
by (res_inst_tac [("C","-r")] real_less_add_left_cancel 1);
by (full_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
qed "real_add_inverse_real_of_posnat_less";
Addsimps [real_add_inverse_real_of_posnat_less];

Goal "r <= r + inverse (real_of_posnat n)";
by (rtac real_less_imp_le 1);
by (Simp_tac 1);
qed "real_add_inverse_real_of_posnat_le";
Addsimps [real_add_inverse_real_of_posnat_le];

Goal "r + (-inverse (real_of_posnat n)) < r";
by (res_inst_tac [("C","-r")] real_less_add_left_cancel 1);
by (full_simp_tac (simpset() addsimps [real_add_assoc RS sym,
				       real_minus_zero_less_iff2]) 1);
qed "real_add_minus_inverse_real_of_posnat_less";
Addsimps [real_add_minus_inverse_real_of_posnat_less];

Goal "r + (-inverse (real_of_posnat n)) <= r";
by (rtac real_less_imp_le 1);
by (Simp_tac 1);
qed "real_add_minus_inverse_real_of_posnat_le";
Addsimps [real_add_minus_inverse_real_of_posnat_le];

Goal "0 < r ==> r*(1r + (-inverse (real_of_posnat n))) < r";
by (simp_tac (simpset() addsimps [real_add_mult_distrib2]) 1);
by (res_inst_tac [("C","-r")] real_less_add_left_cancel 1);
by (auto_tac (claset() addIs [real_mult_order],
	      simpset() addsimps [real_add_assoc RS sym,
				  real_minus_zero_less_iff2]));
qed "real_mult_less_self";

Goal "0 <= 1r + (-inverse (real_of_posnat n))";
by (res_inst_tac [("C","inverse (real_of_posnat n)")] real_le_add_right_cancel 1);
by (simp_tac (simpset() addsimps [real_add_assoc,
				  real_of_posnat_inverse_le_iff]) 1);
qed "real_add_one_minus_inverse_ge_zero";

Goal "0 < r ==> 0 <= r*(1r + (-inverse (real_of_posnat n)))";
by (dtac (real_add_one_minus_inverse_ge_zero RS real_mult_le_less_mono1) 1);
by Auto_tac;
qed "real_mult_add_one_minus_ge_zero";

Goal "(x*y = 0) = (x = 0 | y = (0::real))";
by Auto_tac;
by (blast_tac (claset() addIs [ccontr] addDs [real_mult_not_zero]) 1);
qed "real_mult_is_0";

Goal "(0 = x*y) = (0 = x | (0::real) = y)";
by (stac eq_commute 1 THEN stac real_mult_is_0 1);
by Auto_tac;
qed "real_0_is_mult";
AddIffs [real_mult_is_0, real_0_is_mult];

Goal "[| x ~= 1r; y * x = y |] ==> y = 0";
by (subgoal_tac "y*(1r + -x) = 0" 1);
by (stac real_add_mult_distrib2 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_eq_minus_iff2 RS sym]));
qed "real_mult_eq_self_zero";
Addsimps [real_mult_eq_self_zero];

Goal "[| x ~= 1r; y = y * x |] ==> y = 0";
by (dtac sym 1);
by (Asm_full_simp_tac 1);
qed "real_mult_eq_self_zero2";
Addsimps [real_mult_eq_self_zero2];

Goal "[| 0 <= x * y; 0 < x |] ==> (0::real) <= y";
by (ftac real_inverse_gt_zero 1);
by (dres_inst_tac [("x","inverse x")] real_less_le_mult_order 1);
by (dtac (real_not_refl2 RS not_sym RS real_mult_inv_left) 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_mult_assoc RS sym]));
qed "real_mult_ge_zero_cancel";

Goal "[|x ~= 0; y ~= 0 |] ==> inverse x + inverse y = (x + y) * inverse (x * (y::real))";
by (asm_full_simp_tac (simpset() addsimps 
		       [real_inverse_distrib,real_add_mult_distrib,
			real_mult_assoc RS sym]) 1);
by (stac real_mult_assoc 1);
by (rtac (real_mult_left_commute RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_inverse_add";

(* 05/00 *)
Goal "(0 <= -R) = (R <= (0::real))";
by (auto_tac (claset() addDs [sym],
    simpset() addsimps [real_le_less]));
qed "real_minus_zero_le_iff";

Goal "(-R <= 0) = ((0::real) <= R)";
by (auto_tac (claset(),simpset() addsimps 
    [real_minus_zero_less_iff2,real_le_less]));
qed "real_minus_zero_le_iff2";

Addsimps [real_minus_zero_le_iff, real_minus_zero_le_iff2];

Goal "x * x + y * y = 0 ==> x = (0::real)";
by (dtac real_add_minus_eq_minus 1);
by (cut_inst_tac [("x","x")] real_le_square 1);
by (Auto_tac THEN dtac real_le_anti_sym 1);
by Auto_tac;
qed "real_sum_squares_cancel";

Goal "x * x + y * y = 0 ==> y = (0::real)";
by (res_inst_tac [("y","x")] real_sum_squares_cancel 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_sum_squares_cancel2";

(*----------------------------------------------------------------------------
     Some convenient biconditionals for products of signs (lcp)
 ----------------------------------------------------------------------------*)

Goal "((0::real) < x*y) = (0 < x & 0 < y | x < 0 & y < 0)";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, linorder_not_less, 
                                  real_mult_order, real_mult_less_zero1]));
by (ALLGOALS (rtac ccontr)); 
by (auto_tac (claset(), simpset() addsimps [order_le_less, linorder_not_less]));
by (ALLGOALS (etac rev_mp)); 
by (ALLGOALS (dtac real_mult_less_zero THEN' assume_tac));
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [real_mult_commute]));  
qed "real_zero_less_mult_iff";

Goal "((0::real) <= x*y) = (0 <= x & 0 <= y | x <= 0 & y <= 0)";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, linorder_not_less,  
                                  real_zero_less_mult_iff]));
qed "real_zero_le_mult_iff";

Goal "(x*y < (0::real)) = (0 < x & y < 0 | x < 0 & 0 < y)";
by (auto_tac (claset(), 
              simpset() addsimps [real_zero_le_mult_iff, 
                                  linorder_not_le RS sym]));
by (auto_tac (claset() addDs [order_less_not_sym],  
              simpset() addsimps [linorder_not_le]));
qed "real_mult_less_zero_iff";

Goal "(x*y <= (0::real)) = (0 <= x & y <= 0 | x <= 0 & 0 <= y)";
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [real_zero_less_mult_iff, 
                                  linorder_not_less RS sym]));
qed "real_mult_le_zero_iff";


(*----------------------------------------------------------------------------
     Another embedding of the naturals in the reals (see real_of_posnat)
 ----------------------------------------------------------------------------*)
Goalw [real_of_nat_def] "real_of_nat 0 = 0";
by (simp_tac (simpset() addsimps [real_of_posnat_one]) 1);
qed "real_of_nat_zero";

Goalw [real_of_nat_def] "real_of_nat 1 = 1r";
by (simp_tac (simpset() addsimps [real_of_posnat_two, real_add_assoc]) 1);
qed "real_of_nat_one";
Addsimps [real_of_nat_zero, real_of_nat_one];

Goalw [real_of_nat_def]
     "real_of_nat (m + n) = real_of_nat m + real_of_nat n";
by (simp_tac (simpset() addsimps 
              [real_of_posnat_add,real_add_assoc RS sym]) 1);
qed "real_of_nat_add";

Goalw [real_of_nat_def] "real_of_nat (Suc n) = real_of_nat n + 1r";
by (simp_tac (simpset() addsimps [real_of_posnat_Suc] @ real_add_ac) 1);
qed "real_of_nat_Suc";
Addsimps [real_of_nat_Suc];
    
Goalw [real_of_nat_def] "(real_of_nat n < real_of_nat m) = (n < m)";
by Auto_tac;
qed "real_of_nat_less_iff";

AddIffs [real_of_nat_less_iff];

Goal "inj real_of_nat";
by (rtac injI 1);
by (auto_tac (claset() addSIs [inj_real_of_posnat RS injD],
	      simpset() addsimps [real_of_nat_def,real_add_right_cancel]));
qed "inj_real_of_nat";

Goalw [real_of_nat_def] "0 <= real_of_nat n";
by (res_inst_tac [("C","1r")] real_le_add_right_cancel 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
qed "real_of_nat_ge_zero";
AddIffs [real_of_nat_ge_zero];

Goal "real_of_nat (m * n) = real_of_nat m * real_of_nat n";
by (induct_tac "m" 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_nat_add,
				  real_add_mult_distrib, real_add_commute]));
qed "real_of_nat_mult";

Goal "(real_of_nat n = real_of_nat m) = (n = m)";
by (auto_tac (claset() addDs [inj_real_of_nat RS injD],
              simpset()));
qed "real_of_nat_eq_cancel";

Goal "n <= m --> real_of_nat (m - n) = real_of_nat m + (-real_of_nat n)";
by (induct_tac "m" 1);
by (auto_tac (claset(),
	      simpset() addsimps [Suc_diff_le, le_Suc_eq, real_of_nat_Suc, 
				  real_of_nat_zero] @ real_add_ac));
qed_spec_mp "real_of_nat_minus";

(* 05/00 *)
Goal "n < m ==> real_of_nat (m - n) = \
\     real_of_nat m + -real_of_nat n";
by (auto_tac (claset() addIs [real_of_nat_minus],simpset()));
qed "real_of_nat_minus2";

Goalw [real_diff_def]
     "n < m ==> real_of_nat (m - n) = real_of_nat m - real_of_nat n";
by (etac real_of_nat_minus2 1);
qed "real_of_nat_diff";

Goalw [real_diff_def]
     "n <= m ==> real_of_nat (m - n) = real_of_nat m - real_of_nat n";
by (etac real_of_nat_minus 1);
qed "real_of_nat_diff2";

Goal "(real_of_nat n = 0) = (n = 0)";
by (auto_tac (claset() addIs [inj_real_of_nat RS injD], simpset()));
qed "real_of_nat_zero_iff";
AddIffs [real_of_nat_zero_iff];

Goal "neg z ==> real_of_nat (nat z) = 0";
by (asm_simp_tac (simpset() addsimps [neg_nat, real_of_nat_zero]) 1);
qed "real_of_nat_neg_int";
Addsimps [real_of_nat_neg_int];

