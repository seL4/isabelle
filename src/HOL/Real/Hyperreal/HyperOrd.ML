(*  Title:	 Real/Hyperreal/HyperOrd.ML
    Author:      Jacques D. Fleuriot
    Copyright:   1998 University of Cambridge
                 2000 University of Edinburgh
    Description: Type "hypreal" is a linear order and also 
                 satisfies plus_ac0: + is an AC-operator with zero
*)

(**** The simproc abel_cancel ****)

(*** Two lemmas needed for the simprocs ***)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::hypreal) + (y + z) = y + u) = ((x + z) = u)";
by (stac hypreal_add_left_commute 1);
by (rtac hypreal_add_left_cancel 1);
qed "hypreal_add_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::hypreal) + (y + z) = y) = (x = -z)";
by (stac hypreal_add_left_commute 1);
by (res_inst_tac [("t", "y")] (hypreal_add_zero_right RS subst) 1
    THEN stac hypreal_add_left_cancel 1);
by (simp_tac (simpset() addsimps [hypreal_eq_diff_eq RS sym]) 1);
qed "hypreal_add_cancel_end";


structure Hyperreal_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref		= Sign.self_ref (Theory.sign_of (the_context ()))
  val T			= Type("HyperDef.hypreal",[])
  val zero		= Const ("0", T)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= hypreal_add_cancel_21
  val add_cancel_end	= hypreal_add_cancel_end
  val add_left_cancel	= hypreal_add_left_cancel
  val add_assoc		= hypreal_add_assoc
  val add_commute	= hypreal_add_commute
  val add_left_commute	= hypreal_add_left_commute
  val add_0		= hypreal_add_zero_left
  val add_0_right	= hypreal_add_zero_right

  val eq_diff_eq	= hypreal_eq_diff_eq
  val eqI_rules		= [hypreal_less_eqI, hypreal_eq_eqI, hypreal_le_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= hypreal_diff_def
  val minus_add_distrib	= hypreal_minus_add_distrib
  val minus_minus	= hypreal_minus_minus
  val minus_0		= hypreal_minus_zero
  val add_inverses	= [hypreal_add_minus, hypreal_add_minus_left]
  val cancel_simps	= [hypreal_add_minus_cancelA, hypreal_minus_add_cancelA]
end;

structure Hyperreal_Cancel = Abel_Cancel (Hyperreal_Cancel_Data);

Addsimprocs [Hyperreal_Cancel.sum_conv, Hyperreal_Cancel.rel_conv];

Goal "- (z - y) = y - (z::hypreal)";
by (Simp_tac 1);
qed "hypreal_minus_diff_eq";
Addsimps [hypreal_minus_diff_eq];


Goal "((x::hypreal) < y) = (-y < -x)";
by (stac hypreal_less_minus_iff 1);
by (res_inst_tac [("x1","x")] (hypreal_less_minus_iff RS ssubst) 1);
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_less_swap_iff";

Goalw [hypreal_zero_def] 
      "((0::hypreal) < x) = (-x < x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_less, hypreal_minus]));
by (ALLGOALS(Ultra_tac));
qed "hypreal_gt_zero_iff";

Goal "(A::hypreal) < B ==> A + C < B + C";
by (res_inst_tac [("z","A")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","B")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","C")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [exI], 
              simpset() addsimps [hypreal_less_def,hypreal_add]));
by (Ultra_tac 1);
qed "hypreal_add_less_mono1";

Goal "!!(A::hypreal). A < B ==> C + A < C + B";
by (auto_tac (claset() addIs [hypreal_add_less_mono1],
    simpset() addsimps [hypreal_add_commute]));
qed "hypreal_add_less_mono2";

Goal "(x < (0::hypreal)) = (x < -x)";
by (rtac (hypreal_minus_zero_less_iff RS subst) 1);
by (stac hypreal_gt_zero_iff 1);
by (Full_simp_tac 1);
qed "hypreal_lt_zero_iff";

Goalw [hypreal_le_def] "((0::hypreal) <= x) = (-x <= x)";
by (auto_tac (claset(),simpset() addsimps [hypreal_lt_zero_iff RS sym]));
qed "hypreal_ge_zero_iff";

Goalw [hypreal_le_def] "(x <= (0::hypreal)) = (x <= -x)";
by (auto_tac (claset(),simpset() addsimps [hypreal_gt_zero_iff RS sym]));
qed "hypreal_le_zero_iff";

Goalw [hypreal_zero_def] 
      "[| 0 < x; 0 < y |] ==> (0::hypreal) < x + y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps
    [hypreal_less_def,hypreal_add]));
by (auto_tac (claset() addSIs [exI],simpset() addsimps
    [hypreal_less_def,hypreal_add]));
by (ultra_tac (claset() addIs [real_add_order],simpset()) 1);
qed "hypreal_add_order";

Goal "[| 0 < x; 0 <= y |] ==> (0::hypreal) < x + y";
by (auto_tac (claset() addDs [sym,hypreal_le_imp_less_or_eq]
              addIs [hypreal_add_order],simpset()));
qed "hypreal_add_order_le";            

Goalw [hypreal_zero_def] 
          "[| 0 < x; 0 < y |] ==> (0::hypreal) < x * y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [exI],simpset() addsimps
    [hypreal_less_def,hypreal_mult]));
by (ultra_tac (claset() addIs [rename_numerals real_mult_order],
	       simpset()) 1);
qed "hypreal_mult_order";

Goal "[| x < 0; y < 0 |] ==> (0::hypreal) < x * y";
by (REPEAT(dtac (hypreal_minus_zero_less_iff RS iffD2) 1));
by (dtac hypreal_mult_order 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "hypreal_mult_less_zero1";

Goal "[| 0 <= x; 0 <= y |] ==> (0::hypreal) <= x * y";
by (REPEAT(dtac hypreal_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypreal_mult_order,
    hypreal_less_imp_le],simpset()));
qed "hypreal_le_mult_order";


Goal "[| x <= 0; y <= 0 |] ==> (0::hypreal) <= x * y";
by (rtac hypreal_less_or_eq_imp_le 1);
by (dtac hypreal_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac hypreal_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [hypreal_mult_less_zero1],simpset()));
qed "hypreal_mult_le_zero1";

Goal "[| 0 <= x; y < 0 |] ==> x * y <= (0::hypreal)";
by (rtac hypreal_less_or_eq_imp_le 1);
by (dtac hypreal_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac (hypreal_minus_zero_less_iff RS iffD2) 1);
by (rtac (hypreal_minus_zero_less_iff RS subst) 1);
by (blast_tac (claset() addDs [hypreal_mult_order] 
    addIs [hypreal_minus_mult_eq2 RS ssubst]) 1);
qed "hypreal_mult_le_zero";

Goal "[| 0 < x; y < 0 |] ==> x*y < (0::hypreal)";
by (dtac (hypreal_minus_zero_less_iff RS iffD2) 1);
by (dtac hypreal_mult_order 1 THEN assume_tac 1);
by (rtac (hypreal_minus_zero_less_iff RS iffD1) 1);
by (Asm_full_simp_tac 1);
qed "hypreal_mult_less_zero";

Goalw [hypreal_one_def,hypreal_zero_def,hypreal_less_def] "0 < 1hr";
by (res_inst_tac [("x","%n. #0")] exI 1);
by (res_inst_tac [("x","%n. #1")] exI 1);
by (auto_tac (claset(),
        simpset() addsimps [real_zero_less_one, FreeUltrafilterNat_Nat_set]));
qed "hypreal_zero_less_one";

Goal "1hr < 1hr + 1hr";
by (rtac (hypreal_less_minus_iff RS iffD2) 1);
by (full_simp_tac (simpset() addsimps [hypreal_zero_less_one,
    hypreal_add_assoc]) 1);
qed "hypreal_one_less_two";

Goal "0 < 1hr + 1hr";
by (rtac ([hypreal_zero_less_one,
          hypreal_one_less_two] MRS hypreal_less_trans) 1);
qed "hypreal_zero_less_two";

Goal "1hr + 1hr ~= 0";
by (rtac (hypreal_zero_less_two RS hypreal_not_refl2 RS not_sym) 1);
qed "hypreal_two_not_zero";
Addsimps [hypreal_two_not_zero];

Goal "x/(1hr + 1hr) + x/(1hr + 1hr) = x";
by (stac hypreal_add_self 1);
by (full_simp_tac (simpset() addsimps [hypreal_mult_assoc, hypreal_divide_def,
    hypreal_two_not_zero RS hypreal_mult_inverse_left]) 1);
qed "hypreal_sum_of_halves";

Goal "[| 0 <= x; 0 <= y |] ==> (0::hypreal) <= x + y";
by (REPEAT(dtac hypreal_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypreal_add_order,
    hypreal_less_imp_le],simpset()));
qed "hypreal_le_add_order";

(*** Monotonicity results ***)

Goal "(v+z < w+z) = (v < (w::hypreal))";
by (Simp_tac 1);
qed "hypreal_add_right_cancel_less";

Goal "(z+v < z+w) = (v < (w::hypreal))";
by (Simp_tac 1);
qed "hypreal_add_left_cancel_less";

Addsimps [hypreal_add_right_cancel_less, 
          hypreal_add_left_cancel_less];

Goal "(v+z <= w+z) = (v <= (w::hypreal))";
by (Simp_tac 1);
qed "hypreal_add_right_cancel_le";

Goal "(z+v <= z+w) = (v <= (w::hypreal))";
by (Simp_tac 1);
qed "hypreal_add_left_cancel_le";

Addsimps [hypreal_add_right_cancel_le, hypreal_add_left_cancel_le];

Goal  "[| (z1::hypreal) < y1; z2 < y2 |] ==> z1 + z2 < y1 + y2";
by (dtac (hypreal_less_minus_iff RS iffD1) 1);
by (dtac (hypreal_less_minus_iff RS iffD1) 1);
by (dtac hypreal_add_order 1 THEN assume_tac 1);
by (thin_tac "0 < y2 + - z2" 1);
by (dres_inst_tac [("C","z1 + z2")] hypreal_add_less_mono1 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypreal_minus_add_distrib RS sym] @ hypreal_add_ac
    delsimps [hypreal_minus_add_distrib]));
qed "hypreal_add_less_mono";

Goal "(q1::hypreal) <= q2  ==> x + q1 <= x + q2";
by (dtac hypreal_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [hypreal_le_refl,
    hypreal_less_imp_le,hypreal_add_less_mono1],
    simpset() addsimps [hypreal_add_commute]));
qed "hypreal_add_left_le_mono1";

Goal "(q1::hypreal) <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [hypreal_add_left_le_mono1],
    simpset() addsimps [hypreal_add_commute]));
qed "hypreal_add_le_mono1";

Goal "[|(i::hypreal)<=j;  k<=l |] ==> i + k <= j + l";
by (etac (hypreal_add_le_mono1 RS hypreal_le_trans) 1);
by (Simp_tac 1);
qed "hypreal_add_le_mono";

Goal "[|(i::hypreal)<j;  k<=l |] ==> i + k < j + l";
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq] 
    addIs [hypreal_add_less_mono1,hypreal_add_less_mono],
    simpset()));
qed "hypreal_add_less_le_mono";

Goal "[|(i::hypreal)<=j;  k<l |] ==> i + k < j + l";
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq] 
    addIs [hypreal_add_less_mono2,hypreal_add_less_mono],simpset()));
qed "hypreal_add_le_less_mono";

Goal "(A::hypreal) + C < B + C ==> A < B";
by (Full_simp_tac 1);
qed "hypreal_less_add_right_cancel";

Goal "(C::hypreal) + A < C + B ==> A < B";
by (Full_simp_tac 1);
qed "hypreal_less_add_left_cancel";

Goal "[|r < x; (0::hypreal) <= y|] ==> r < x + y";
by (auto_tac (claset() addDs [hypreal_add_less_le_mono],
    simpset()));
qed "hypreal_add_zero_less_le_mono";

Goal "!!(A::hypreal). A + C <= B + C ==> A <= B";
by (dres_inst_tac [("x","-C")] hypreal_add_le_mono1 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc]) 1);
qed "hypreal_le_add_right_cancel";

Goal "!!(A::hypreal). C + A <= C + B ==> A <= B";
by (dres_inst_tac [("x","-C")] hypreal_add_left_le_mono1 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_le_add_left_cancel";

Goal "(0::hypreal) <= x*x";
by (res_inst_tac [("x","0"),("y","x")] hypreal_linear_less2 1);
by (auto_tac (claset() addIs [hypreal_mult_order,
    hypreal_mult_less_zero1,hypreal_less_imp_le],
    simpset()));
qed "hypreal_le_square";
Addsimps [hypreal_le_square];

Goalw [hypreal_le_def] "- (x*x) <= (0::hypreal)";
by (auto_tac (claset() addSDs [(hypreal_le_square RS 
    hypreal_le_less_trans)],simpset() addsimps 
    [hypreal_minus_zero_less_iff,hypreal_less_not_refl]));
qed "hypreal_less_minus_square";
Addsimps [hypreal_less_minus_square];

Goal "(0*x<r)=((0::hypreal)<r)";
by (Simp_tac 1);
qed "hypreal_mult_0_less";

Goal "[| (0::hypreal) < z; x < y |] ==> x*z < y*z";       
by (rotate_tac 1 1);
by (dtac (hypreal_less_minus_iff RS iffD1) 1);
by (rtac (hypreal_less_minus_iff RS iffD2) 1);
by (dtac hypreal_mult_order 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_mult_distrib2,
					   hypreal_mult_commute ]) 1);
qed "hypreal_mult_less_mono1";

Goal "[| (0::hypreal)<z; x<y |] ==> z*x<z*y";       
by (asm_simp_tac (simpset() addsimps [hypreal_mult_commute,hypreal_mult_less_mono1]) 1);
qed "hypreal_mult_less_mono2";

Goal "[| (0::hypreal)<=z; x<y |] ==> x*z<=y*z";
by (EVERY1 [rtac hypreal_less_or_eq_imp_le, dtac hypreal_le_imp_less_or_eq]);
by (auto_tac (claset() addIs [hypreal_mult_less_mono1],simpset()));
qed "hypreal_mult_le_less_mono1";

Goal "[| (0::hypreal)<=z; x<y |] ==> z*x<=z*y";
by (asm_simp_tac (simpset() addsimps [hypreal_mult_commute,
				      hypreal_mult_le_less_mono1]) 1);
qed "hypreal_mult_le_less_mono2";

Goal "[| (0::hypreal)<=z; x<=y |] ==> z*x<=z*y";
by (dres_inst_tac [("x","x")] hypreal_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [hypreal_mult_le_less_mono2,hypreal_le_refl],simpset()));
qed "hypreal_mult_le_le_mono1";

val prem1::prem2::prem3::rest = goal thy
     "[| (0::hypreal)<y; x<r; y*r<t*s |] ==> y*x<t*s";
by (rtac ([([prem1,prem2] MRS hypreal_mult_less_mono2),prem3] MRS hypreal_less_trans) 1);
qed "hypreal_mult_less_trans";

Goal "[| 0<=y; x<r; y*r<t*s; (0::hypreal)<t*s|] ==> y*x<t*s";
by (dtac hypreal_le_imp_less_or_eq 1);
by (fast_tac (HOL_cs addEs [(hypreal_mult_0_less RS iffD2),hypreal_mult_less_trans]) 1);
qed "hypreal_mult_le_less_trans";

Goal "[| 0 <= y; x <= r; y*r < t*s; (0::hypreal) < t*s|] ==> y*x < t*s";
by (dres_inst_tac [("x","x")] hypreal_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [hypreal_mult_le_less_trans]) 1);
qed "hypreal_mult_le_le_trans";

Goal "[| 0 < r1; r1 <r2; (0::hypreal) < x; x < y|] \
\                     ==> r1 * x < r2 * y";
by (dres_inst_tac [("x","x")] hypreal_mult_less_mono2 1);
by (dres_inst_tac [("R1.0","0")] hypreal_less_trans 2);
by (dres_inst_tac [("x","r1")] hypreal_mult_less_mono1 3);
by Auto_tac;
by (blast_tac (claset() addIs [hypreal_less_trans]) 1);
qed "hypreal_mult_less_mono";

Goal "[| 0 < r1; r1 <r2; 0 < y|] \
\                           ==> (0::hypreal) < r2 * y";
by (dres_inst_tac [("R1.0","0")] hypreal_less_trans 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [hypreal_mult_order]) 1);
qed "hypreal_mult_order_trans";

Goal "[| 0 < r1; r1 <= r2; (0::hypreal) <= x; x <= y |] \
\                  ==> r1 * x <= r2 * y";
by (rtac hypreal_less_or_eq_imp_le 1);
by (REPEAT(dtac hypreal_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypreal_mult_less_mono,
    hypreal_mult_less_mono1,hypreal_mult_less_mono2,
    hypreal_mult_order_trans,hypreal_mult_order],simpset()));
qed "hypreal_mult_le_mono";

Goal "0 < x ==> 0 < inverse (x::hypreal)";
by (EVERY1[rtac ccontr, dtac hypreal_leI]);
by (forward_tac [hypreal_minus_zero_less_iff2 RS iffD2] 1);
by (forward_tac [hypreal_not_refl2 RS not_sym] 1);
by (dtac (hypreal_not_refl2 RS not_sym RS hypreal_inverse_not_zero) 1);
by (EVERY1[dtac hypreal_le_imp_less_or_eq, Step_tac]); 
by (dtac hypreal_mult_less_zero1 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [hypreal_zero_less_one RS hypreal_less_asym],
    simpset() addsimps [hypreal_minus_zero_less_iff]));
qed "hypreal_inverse_gt_zero";

Goal "x < 0 ==> inverse (x::hypreal) < 0";
by (ftac hypreal_not_refl2 1);
by (dtac (hypreal_minus_zero_less_iff RS iffD2) 1);
by (rtac (hypreal_minus_zero_less_iff RS iffD1) 1);
by (stac (hypreal_minus_inverse RS sym) 1);
by (auto_tac (claset() addIs [hypreal_inverse_gt_zero],  simpset()));
qed "hypreal_inverse_less_zero";

(* check why this does not work without 2nd substitution anymore! *)
Goal "x < y ==> x < (x + y)*inverse(1hr + 1hr)";
by (dres_inst_tac [("C","x")] hypreal_add_less_mono2 1);
by (dtac (hypreal_add_self RS subst) 1);
by (dtac (hypreal_zero_less_two RS hypreal_inverse_gt_zero RS 
          hypreal_mult_less_mono1) 1);
by (auto_tac (claset() addDs [hypreal_two_not_zero RS 
          (hypreal_mult_inverse RS subst)],simpset() 
          addsimps [hypreal_mult_assoc]));
qed "hypreal_less_half_sum";

(* check why this does not work without 2nd substitution anymore! *)
Goal "x < y ==> (x + y)*inverse(1hr + 1hr) < y";
by (dres_inst_tac [("C","y")] hypreal_add_less_mono1 1);
by (dtac (hypreal_add_self RS subst) 1);
by (dtac (hypreal_zero_less_two RS hypreal_inverse_gt_zero RS 
          hypreal_mult_less_mono1) 1);
by (auto_tac (claset() addDs [hypreal_two_not_zero RS 
          (hypreal_mult_inverse RS subst)],simpset() 
          addsimps [hypreal_mult_assoc]));
qed "hypreal_gt_half_sum";

Goal "!!(x::hypreal). x < y ==> EX r. x < r & r < y";
by (blast_tac (claset() addSIs [hypreal_less_half_sum,
                                hypreal_gt_half_sum]) 1);
qed "hypreal_dense";


(*?? more needed and earlier??*)
Goal "(x+y = (0::hypreal)) = (x = -y)";
by (stac hypreal_eq_minus_iff 1);
by Auto_tac;
qed "hypreal_add_eq_0_iff";
AddIffs [hypreal_add_eq_0_iff];

Goal "[| 0 <= x; 0 <= y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))";
by (auto_tac (claset() addIs [order_antisym], simpset()));
qed "hypreal_add_nonneg_eq_0_iff";

Goal "(x*x + y*y = 0) = (x = 0 & y = (0::hypreal))";
by (simp_tac
    (HOL_ss addsimps [hypreal_le_square, hypreal_add_nonneg_eq_0_iff]) 1);
by Auto_tac;
qed "hypreal_squares_add_zero_iff";
Addsimps [hypreal_squares_add_zero_iff];

Goal "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))";
by (simp_tac (HOL_ss addsimps [hypreal_le_square, hypreal_le_add_order, 
                               hypreal_add_nonneg_eq_0_iff]) 1);
by Auto_tac;
qed "hypreal_three_squares_add_zero_iff";
Addsimps [hypreal_three_squares_add_zero_iff];

Addsimps [rename_numerals real_le_square];

Goal "(x::hypreal)*x <= x*x + y*y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_mult,hypreal_add,hypreal_le]));
qed "hypreal_self_le_add_pos";
Addsimps [hypreal_self_le_add_pos];

(*lcp: new lemma unfortunately needed...*)
Goal "-(x*x) <= (y*y::real)";
by (rtac order_trans 1);
by (rtac real_le_square 2);
by Auto_tac;
qed "minus_square_le_square";

Goal "(x::hypreal)*x <= x*x + y*y + z*z";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
	      simpset() addsimps [hypreal_mult, hypreal_add, hypreal_le,
				  minus_square_le_square]));
qed "hypreal_self_le_add_pos2";
Addsimps [hypreal_self_le_add_pos2];


(*----------------------------------------------------------------------------
             Embedding of the naturals in the hyperreals
 ----------------------------------------------------------------------------*)
Goalw [hypreal_of_posnat_def] "hypreal_of_posnat 0 = 1hr";
by (full_simp_tac (simpset() addsimps 
    [pnat_one_iff RS sym,real_of_preal_def]) 1);
by (fold_tac [real_one_def]);
by (simp_tac (simpset() addsimps [hypreal_of_real_one]) 1);
qed "hypreal_of_posnat_one";

Goalw [hypreal_of_posnat_def] "hypreal_of_posnat 1 = 1hr + 1hr";
by (full_simp_tac (simpset() addsimps 
		   [real_of_preal_def,
		    rename_numerals (real_one_def RS meta_eq_to_obj_eq),
		    hypreal_add,hypreal_of_real_def,pnat_two_eq,
		    hypreal_one_def, real_add,
		    prat_of_pnat_add RS sym, preal_of_prat_add RS sym] @ 
		    pnat_add_ac) 1);
qed "hypreal_of_posnat_two";

Goalw [hypreal_of_posnat_def]
          "hypreal_of_posnat n1 + hypreal_of_posnat n2 = \
\          hypreal_of_posnat (n1 + n2) + 1hr";
by (full_simp_tac (simpset() addsimps [hypreal_of_posnat_one RS sym,
    hypreal_of_real_add RS sym,hypreal_of_posnat_def,real_of_preal_add RS sym,
    preal_of_prat_add RS sym,prat_of_pnat_add RS sym,pnat_of_nat_add]) 1);
qed "hypreal_of_posnat_add";

Goal "hypreal_of_posnat (n + 1) = hypreal_of_posnat n + 1hr";
by (res_inst_tac [("x1","1hr")] (hypreal_add_right_cancel RS iffD1) 1);
by (rtac (hypreal_of_posnat_add RS subst) 1);
by (full_simp_tac (simpset() addsimps [hypreal_of_posnat_two,hypreal_add_assoc]) 1);
qed "hypreal_of_posnat_add_one";

Goalw [real_of_posnat_def,hypreal_of_posnat_def] 
      "hypreal_of_posnat n = hypreal_of_real (real_of_posnat n)";
by (rtac refl 1);
qed "hypreal_of_real_of_posnat";

Goalw [hypreal_of_posnat_def] 
      "(n < m) = (hypreal_of_posnat n < hypreal_of_posnat m)";
by Auto_tac;
qed "hypreal_of_posnat_less_iff";

Addsimps [hypreal_of_posnat_less_iff RS sym];
(*---------------------------------------------------------------------------------
               Existence of infinite hyperreal number
 ---------------------------------------------------------------------------------*)

Goal "hyprel^^{%n::nat. real_of_posnat n} : hypreal";
by Auto_tac;
qed "hypreal_omega";

Goalw [omega_def] "Rep_hypreal(whr) : hypreal";
by (rtac Rep_hypreal 1);
qed "Rep_hypreal_omega";

(* existence of infinite number not corresponding to any real number *)
(* use assumption that member FreeUltrafilterNat is not finite       *)
(* a few lemmas first *)

Goal "{n::nat. x = real_of_posnat n} = {} | \
\     (EX y. {n::nat. x = real_of_posnat n} = {y})";
by (auto_tac (claset() addDs [inj_real_of_posnat RS injD],simpset()));
qed "lemma_omega_empty_singleton_disj";

Goal "finite {n::nat. x = real_of_posnat n}";
by (cut_inst_tac [("x","x")] lemma_omega_empty_singleton_disj 1);
by Auto_tac;
qed "lemma_finite_omega_set";

Goalw [omega_def,hypreal_of_real_def] 
      "~ (EX x. hypreal_of_real x = whr)";
by (auto_tac (claset(),simpset() addsimps [lemma_finite_omega_set 
    RS FreeUltrafilterNat_finite]));
qed "not_ex_hypreal_of_real_eq_omega";

Goal "hypreal_of_real x ~= whr";
by (cut_facts_tac [not_ex_hypreal_of_real_eq_omega] 1);
by Auto_tac;
qed "hypreal_of_real_not_eq_omega";

(* existence of infinitesimal number also not *)
(* corresponding to any real number *)

Goal "{n::nat. x = inverse(real_of_posnat n)} = {} | \
\     (EX y. {n::nat. x = inverse(real_of_posnat n)} = {y})";
by (Step_tac 1 THEN Step_tac 1);
by (auto_tac (claset() addIs [real_of_posnat_inverse_inj],simpset()));
qed "lemma_epsilon_empty_singleton_disj";

Goal "finite {n::nat. x = inverse(real_of_posnat n)}";
by (cut_inst_tac [("x","x")] lemma_epsilon_empty_singleton_disj 1);
by Auto_tac;
qed "lemma_finite_epsilon_set";

Goalw [epsilon_def,hypreal_of_real_def] 
      "~ (EX x. hypreal_of_real x = ehr)";
by (auto_tac (claset(),simpset() addsimps [lemma_finite_epsilon_set 
    RS FreeUltrafilterNat_finite]));
qed "not_ex_hypreal_of_real_eq_epsilon";

Goal "hypreal_of_real x ~= ehr";
by (cut_facts_tac [not_ex_hypreal_of_real_eq_epsilon] 1);
by Auto_tac;
qed "hypreal_of_real_not_eq_epsilon";

Goalw [epsilon_def,hypreal_zero_def] "ehr ~= 0";
by (auto_tac (claset(),
     simpset() addsimps [rename_numerals real_of_posnat_not_eq_zero]));
qed "hypreal_epsilon_not_zero";

Addsimps [rename_numerals real_of_posnat_not_eq_zero];
Goalw [omega_def,hypreal_zero_def] "whr ~= 0";
by (Simp_tac 1);
qed "hypreal_omega_not_zero";

Goal "ehr = inverse(whr)";
by (asm_full_simp_tac (simpset() addsimps 
                     [hypreal_inverse, omega_def, epsilon_def]) 1);
qed "hypreal_epsilon_inverse_omega";

(*----------------------------------------------------------------
     Another embedding of the naturals in the 
    hyperreals (see hypreal_of_posnat)
 ----------------------------------------------------------------*)
Goalw [hypreal_of_nat_def] "hypreal_of_nat 0 = 0";
by (full_simp_tac (simpset() addsimps [hypreal_of_posnat_one]) 1);
qed "hypreal_of_nat_zero";

Goalw [hypreal_of_nat_def] "hypreal_of_nat 1 = 1hr";
by (full_simp_tac (simpset() addsimps [hypreal_of_posnat_two,
                                       hypreal_add_assoc]) 1);
qed "hypreal_of_nat_one";

Goalw [hypreal_of_nat_def]
      "hypreal_of_nat n1 + hypreal_of_nat n2 = \
\      hypreal_of_nat (n1 + n2)";
by (full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
by (simp_tac (simpset() addsimps [hypreal_of_posnat_add,
    hypreal_add_assoc RS sym]) 1);
qed "hypreal_of_nat_add";

Goal "hypreal_of_nat 2 = 1hr + 1hr";
by (simp_tac (simpset() addsimps [hypreal_of_nat_one 
    RS sym,hypreal_of_nat_add]) 1);
qed "hypreal_of_nat_two";

Goalw [hypreal_of_nat_def] 
      "(n < m) = (hypreal_of_nat n < hypreal_of_nat m)";
by (auto_tac (claset() addIs [hypreal_add_less_mono1],simpset()));
qed "hypreal_of_nat_less_iff";
Addsimps [hypreal_of_nat_less_iff RS sym];

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

Goalw [hypreal_of_nat_def,real_of_nat_def] 
      "hypreal_of_nat  m = Abs_hypreal(hyprel^^{%n. real_of_nat m})";
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_def,
    hypreal_of_real_of_posnat,hypreal_minus,hypreal_one_def,hypreal_add]));
qed "hypreal_of_nat_iff";

Goal "inj hypreal_of_nat";
by (rtac injI 1);
by (auto_tac (claset() addSDs [FreeUltrafilterNat_P],
        simpset() addsimps [split_if_mem1, hypreal_of_nat_iff,
        real_add_right_cancel,inj_real_of_nat RS injD]));
qed "inj_hypreal_of_nat";

Goalw [hypreal_of_nat_def,hypreal_of_real_def,hypreal_of_posnat_def,
       real_of_posnat_def,hypreal_one_def,real_of_nat_def] 
       "hypreal_of_nat n = hypreal_of_real (real_of_nat n)";
by (simp_tac (simpset() addsimps [hypreal_add,hypreal_minus]) 1);
qed "hypreal_of_nat_real_of_nat";

Goal "hypreal_of_posnat (Suc n) = hypreal_of_posnat n + 1hr";
by (stac (hypreal_of_posnat_add_one RS sym) 1);
by (Simp_tac 1);
qed "hypreal_of_posnat_Suc";

Goalw [hypreal_of_nat_def] 
      "hypreal_of_nat (Suc n) = hypreal_of_nat n + 1hr";
by (simp_tac (simpset() addsimps [hypreal_of_posnat_Suc] @ hypreal_add_ac) 1);
qed "hypreal_of_nat_Suc";

Goal "0 < r ==> 0 < r/(1hr+1hr)";
by (dtac (hypreal_zero_less_two RS hypreal_inverse_gt_zero 
          RS hypreal_mult_less_mono1) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_divide_def]));
qed "hypreal_half_gt_zero";

(* this proof is so much simpler than one for reals!! *)
Goal "[| 0 < r; r < x |] ==> inverse x < inverse (r::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_inverse,
    hypreal_less,hypreal_zero_def]));
by (ultra_tac (claset() addIs [real_inverse_less_swap],simpset()) 1);
qed "hypreal_inverse_less_swap";

Goal "[| 0 < r; 0 < x|] ==> (r < x) = (inverse x < inverse (r::hypreal))";
by (auto_tac (claset() addIs [hypreal_inverse_less_swap],simpset()));
by (res_inst_tac [("t","r")] (hypreal_inverse_inverse RS subst) 1);
by (res_inst_tac [("t","x")] (hypreal_inverse_inverse RS subst) 1);
by (rtac hypreal_inverse_less_swap 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_inverse_gt_zero]));
qed "hypreal_inverse_less_iff";

Goal "[| 0 < z; x < y |] ==> x * inverse z < y * inverse (z::hypreal)";
by (blast_tac (claset() addSIs [hypreal_mult_less_mono1,
                                hypreal_inverse_gt_zero]) 1);
qed "hypreal_mult_inverse_less_mono1";

Goal "[| 0 < z; x < y |] ==> inverse z * x < inverse (z::hypreal) * y";
by (blast_tac (claset() addSIs [hypreal_mult_less_mono2,
                                hypreal_inverse_gt_zero]) 1);
qed "hypreal_mult_inverse_less_mono2";

Goal "[| (0::hypreal) < z; x*z < y*z |] ==> x < y";
by (forw_inst_tac [("x","x*z")] hypreal_mult_inverse_less_mono1 1);
by (dtac (hypreal_not_refl2 RS not_sym) 2);
by (auto_tac (claset() addSDs [hypreal_mult_inverse],
              simpset() addsimps hypreal_mult_ac));
qed "hypreal_less_mult_right_cancel";

Goal "[| (0::hypreal) < z; z*x < z*y |] ==> x < y";
by (auto_tac (claset() addIs [hypreal_less_mult_right_cancel],
    simpset() addsimps [hypreal_mult_commute]));
qed "hypreal_less_mult_left_cancel";

Goal "[| 0 < r; (0::hypreal) < ra; r < x; ra < y |] ==> r*ra < x*y";
by (forw_inst_tac [("R2.0","r")] hypreal_less_trans 1);
by (dres_inst_tac [("z","ra"),("x","r")] hypreal_mult_less_mono1 2);
by (dres_inst_tac [("z","x"),("x","ra")] hypreal_mult_less_mono2 3);
by (auto_tac (claset() addIs [hypreal_less_trans],simpset()));
qed "hypreal_mult_less_gt_zero"; 

Goal "[| 0 < r; (0::hypreal) < ra; r <= x; ra <= y |] ==> r*ra <= x*y";
by (REPEAT(dtac hypreal_le_imp_less_or_eq 1));
by (rtac hypreal_less_or_eq_imp_le 1);
by (auto_tac (claset() addIs [hypreal_mult_less_mono1,
    hypreal_mult_less_mono2,hypreal_mult_less_gt_zero],
    simpset()));
qed "hypreal_mult_le_ge_zero"; 

(*----------------------------------------------------------------------------
     Some convenient biconditionals for products of signs 
 ----------------------------------------------------------------------------*)

Goal "((0::hypreal) < x*y) = (0 < x & 0 < y | x < 0 & y < 0)";
 by (auto_tac (claset(), 
               simpset() addsimps [order_le_less, linorder_not_less, 
                              hypreal_mult_order, hypreal_mult_less_zero1]));
by (ALLGOALS (rtac ccontr)); 
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, linorder_not_less]));
by (ALLGOALS (etac rev_mp)); 
by (ALLGOALS (dtac hypreal_mult_less_zero THEN' assume_tac));
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [hypreal_mult_commute]));  
qed "hypreal_zero_less_mult_iff";

Goal "((0::hypreal) <= x*y) = (0 <= x & 0 <= y | x <= 0 & y <= 0)";
by (auto_tac (claset() addDs [hypreal_mult_zero_disj],
              simpset() addsimps [order_le_less, linorder_not_less,
                                  hypreal_zero_less_mult_iff]));
qed "hypreal_zero_le_mult_iff";

Goal "(x*y < (0::hypreal)) = (0 < x & y < 0 | x < 0 & 0 < y)";
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_zero_le_mult_iff, 
                                  linorder_not_le RS sym]));
by (auto_tac (claset() addDs [order_less_not_sym],  
              simpset() addsimps [linorder_not_le]));
qed "hypreal_mult_less_zero_iff";

Goal "(x*y <= (0::hypreal)) = (0 <= x & y <= 0 | x <= 0 & 0 <= y)";
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [hypreal_zero_less_mult_iff, 
                                  linorder_not_less RS sym]));
qed "hypreal_mult_le_zero_iff";

