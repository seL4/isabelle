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

Goalw [hypreal_zero_def] "[| 0 < x; 0 < y |] ==> (0::hypreal) < x + y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_less_def,hypreal_add]));
by (auto_tac (claset() addSIs [exI],
              simpset() addsimps [hypreal_less_def,hypreal_add]));
by (ultra_tac (claset() addIs [real_add_order], simpset()) 1);
qed "hypreal_add_order";

Goal "[| 0 < x; 0 <= y |] ==> (0::hypreal) < x + y";
by (auto_tac (claset() addDs [sym, order_le_imp_less_or_eq]
                       addIs [hypreal_add_order],
              simpset()));
qed "hypreal_add_order_le";            

Goalw [hypreal_zero_def] "[| 0 < x; 0 < y |] ==> (0::hypreal) < x * y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [exI],
              simpset() addsimps [hypreal_less_def,hypreal_mult]));
by (ultra_tac (claset() addIs [real_mult_order], simpset()) 1);
qed "hypreal_mult_order";

Goal "[| x < 0; y < 0 |] ==> (0::hypreal) < x * y";
by (REPEAT(dtac (hypreal_minus_zero_less_iff RS iffD2) 1));
by (dtac hypreal_mult_order 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "hypreal_mult_less_zero1";

Goal "[| 0 < x; y < 0 |] ==> x*y < (0::hypreal)";
by (dtac (hypreal_minus_zero_less_iff RS iffD2) 1);
by (dtac hypreal_mult_order 1 THEN assume_tac 1);
by (rtac (hypreal_minus_zero_less_iff RS iffD1) 1);
by (Asm_full_simp_tac 1);
qed "hypreal_mult_less_zero";

Goalw [hypreal_one_def,hypreal_zero_def,hypreal_less_def] "0 < (1::hypreal)";
by (res_inst_tac [("x","%n. 0")] exI 1);
by (res_inst_tac [("x","%n. 1")] exI 1);
by (auto_tac (claset(),
        simpset() addsimps [real_zero_less_one, FreeUltrafilterNat_Nat_set]));
qed "hypreal_zero_less_one";

Goal "[| 0 <= x; 0 <= y |] ==> (0::hypreal) <= x + y";
by (REPEAT(dtac order_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypreal_add_order, order_less_imp_le],
              simpset()));
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
by (auto_tac (claset(),
      simpset() addsimps [hypreal_minus_add_distrib RS sym] @ hypreal_add_ac
                delsimps [hypreal_minus_add_distrib]));
qed "hypreal_add_less_mono";

Goal "(q1::hypreal) <= q2  ==> x + q1 <= x + q2";
by (dtac order_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [order_less_imp_le,hypreal_add_less_mono1],
              simpset() addsimps [hypreal_add_commute]));
qed "hypreal_add_left_le_mono1";

Goal "(q1::hypreal) <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [hypreal_add_left_le_mono1],
              simpset() addsimps [hypreal_add_commute]));
qed "hypreal_add_le_mono1";

Goal "[|(i::hypreal)<=j;  k<=l |] ==> i + k <= j + l";
by (etac (hypreal_add_le_mono1 RS order_trans) 1);
by (Simp_tac 1);
qed "hypreal_add_le_mono";

Goal "[|(i::hypreal)<j;  k<=l |] ==> i + k < j + l";
by (auto_tac (claset() addSDs [order_le_imp_less_or_eq] 
                       addIs [hypreal_add_less_mono1,hypreal_add_less_mono],
    simpset()));
qed "hypreal_add_less_le_mono";

Goal "[|(i::hypreal)<=j;  k<l |] ==> i + k < j + l";
by (auto_tac (claset() addSDs [order_le_imp_less_or_eq] 
                       addIs [hypreal_add_less_mono2,hypreal_add_less_mono],
              simpset()));
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
                              hypreal_mult_less_zero1,order_less_imp_le],
              simpset()));
qed "hypreal_le_square";
Addsimps [hypreal_le_square];

Goalw [hypreal_le_def] "- (x*x) <= (0::hypreal)";
by (auto_tac (claset() addSDs [hypreal_le_square RS order_le_less_trans],
      simpset() addsimps [hypreal_minus_zero_less_iff]));
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
by (EVERY1 [rtac hypreal_less_or_eq_imp_le, dtac order_le_imp_less_or_eq]);
by (auto_tac (claset() addIs [hypreal_mult_less_mono1], simpset()));
qed "hypreal_mult_le_less_mono1";

Goal "[| (0::hypreal)<=z; x<y |] ==> z*x<=z*y";
by (asm_simp_tac (simpset() addsimps [hypreal_mult_commute,
				      hypreal_mult_le_less_mono1]) 1);
qed "hypreal_mult_le_less_mono2";

val prem1::prem2::prem3::rest = goal thy
     "[| (0::hypreal)<y; x<r; y*r<t*s |] ==> y*x<t*s";
by (rtac ([[prem1,prem2] MRS hypreal_mult_less_mono2, prem3] 
          MRS order_less_trans) 1);
qed "hypreal_mult_less_trans";

Goal "[| 0<=y; x<r; y*r<t*s; (0::hypreal)<t*s|] ==> y*x<t*s";
by (dtac order_le_imp_less_or_eq 1);
by (fast_tac (HOL_cs addEs [hypreal_mult_0_less RS iffD2,
                            hypreal_mult_less_trans]) 1);
qed "hypreal_mult_le_less_trans";

Goal "[| 0 <= y; x <= r; y*r < t*s; (0::hypreal) < t*s|] ==> y*x < t*s";
by (dres_inst_tac [("x","x")] order_le_imp_less_or_eq 1);
by (fast_tac (claset() addIs [hypreal_mult_le_less_trans]) 1);
qed "hypreal_mult_le_le_trans";

Goal "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y";
by (etac (hypreal_mult_less_mono1 RS order_less_trans) 1);
by (assume_tac 1);
by (etac hypreal_mult_less_mono2 1);
by (assume_tac 1);
qed "hypreal_mult_less_mono";

(*UNUSED at present but possibly more useful than hypreal_mult_less_mono*)
Goal "[| x < y;  r1 < r2;  (0::hypreal) <= r1;  0 <= x|] ==> r1 * x < r2 * y";
by (subgoal_tac "0<r2" 1);
by (blast_tac (claset() addIs [order_le_less_trans]) 2); 
by (case_tac "x=0" 1);
by (auto_tac (claset() addSDs [order_le_imp_less_or_eq] 
	               addIs [hypreal_mult_less_mono, hypreal_mult_order],
	      simpset()));
qed "hypreal_mult_less_mono'";

Goal "0 < x ==> 0 < inverse (x::hypreal)";
by (EVERY1[rtac ccontr, dtac hypreal_leI]);
by (forward_tac [hypreal_minus_zero_less_iff2 RS iffD2] 1);
by (forward_tac [hypreal_not_refl2 RS not_sym] 1);
by (dtac (hypreal_not_refl2 RS not_sym RS hypreal_inverse_not_zero) 1);
by (EVERY1[dtac order_le_imp_less_or_eq, Step_tac]); 
by (dtac hypreal_mult_less_zero1 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [hypreal_zero_less_one RS hypreal_less_asym],
                 simpset() addsimps [hypreal_minus_zero_less_iff]));
qed "hypreal_inverse_gt_0";

Goal "x < 0 ==> inverse (x::hypreal) < 0";
by (ftac hypreal_not_refl2 1);
by (dtac (hypreal_minus_zero_less_iff RS iffD2) 1);
by (rtac (hypreal_minus_zero_less_iff RS iffD1) 1);
by (stac (hypreal_minus_inverse RS sym) 1);
by (auto_tac (claset() addIs [hypreal_inverse_gt_0],  simpset()));
qed "hypreal_inverse_less_0";

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
               Existence of infinite hyperreal number
 ----------------------------------------------------------------------------*)

Goalw [omega_def] "Rep_hypreal(omega) : hypreal";
by (rtac Rep_hypreal 1);
qed "Rep_hypreal_omega";

(* existence of infinite number not corresponding to any real number *)
(* use assumption that member FreeUltrafilterNat is not finite       *)
(* a few lemmas first *)

Goal "{n::nat. x = real n} = {} | \
\     (EX y. {n::nat. x = real n} = {y})";
by (auto_tac (claset() addDs [inj_real_of_nat RS injD], simpset()));
qed "lemma_omega_empty_singleton_disj";

Goal "finite {n::nat. x = real n}";
by (cut_inst_tac [("x","x")] lemma_omega_empty_singleton_disj 1);
by Auto_tac;
qed "lemma_finite_omega_set";

Goalw [omega_def,hypreal_of_real_def] 
      "~ (EX x. hypreal_of_real x = omega)";
by (auto_tac (claset(),
    simpset() addsimps [real_of_nat_Suc, diff_eq_eq RS sym, 
                    lemma_finite_omega_set RS FreeUltrafilterNat_finite]));
qed "not_ex_hypreal_of_real_eq_omega";

Goal "hypreal_of_real x ~= omega";
by (cut_facts_tac [not_ex_hypreal_of_real_eq_omega] 1);
by Auto_tac;
qed "hypreal_of_real_not_eq_omega";

(* existence of infinitesimal number also not *)
(* corresponding to any real number *)

Goal "inverse (real (x::nat)) = inverse (real y) ==> x = y";
by (rtac (inj_real_of_nat RS injD) 1);
by (Asm_full_simp_tac 1); 
qed "real_of_nat_inverse_inj";

Goal "{n::nat. x = inverse(real(Suc n))} = {} | \
\     (EX y. {n::nat. x = inverse(real(Suc n))} = {y})";
by (auto_tac (claset(), simpset() addsimps [inj_real_of_nat RS inj_eq]));
qed "lemma_epsilon_empty_singleton_disj";

Goal "finite {n. x = inverse(real(Suc n))}";
by (cut_inst_tac [("x","x")] lemma_epsilon_empty_singleton_disj 1);
by Auto_tac;
qed "lemma_finite_epsilon_set";

Goalw [epsilon_def,hypreal_of_real_def] 
      "~ (EX x. hypreal_of_real x = epsilon)";
by (auto_tac (claset(),
  simpset() addsimps [lemma_finite_epsilon_set RS FreeUltrafilterNat_finite]));
qed "not_ex_hypreal_of_real_eq_epsilon";

Goal "hypreal_of_real x ~= epsilon";
by (cut_facts_tac [not_ex_hypreal_of_real_eq_epsilon] 1);
by Auto_tac;
qed "hypreal_of_real_not_eq_epsilon";

Goalw [epsilon_def,hypreal_zero_def] "epsilon ~= 0";
by Auto_tac;  
by (auto_tac (claset(),
     simpset() addsimps [real_of_nat_Suc_gt_zero RS real_not_refl2 RS not_sym]));
qed "hypreal_epsilon_not_zero";

Goal "epsilon = inverse(omega)";
by (asm_full_simp_tac (simpset() addsimps 
                     [hypreal_inverse, omega_def, epsilon_def]) 1);
qed "hypreal_epsilon_inverse_omega";


(* this proof is so much simpler than one for reals!! *)
Goal "[| 0 < r; r < x |] ==> inverse x < inverse (r::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
      simpset() addsimps [hypreal_inverse, hypreal_less,hypreal_zero_def]));
by (ultra_tac (claset() addIs [real_inverse_less_swap], simpset()) 1);
qed "hypreal_inverse_less_swap";

Goal "[| 0 < r; 0 < x|] ==> (r < x) = (inverse x < inverse (r::hypreal))";
by (auto_tac (claset() addIs [hypreal_inverse_less_swap], simpset()));
by (res_inst_tac [("t","r")] (hypreal_inverse_inverse RS subst) 1);
by (res_inst_tac [("t","x")] (hypreal_inverse_inverse RS subst) 1);
by (rtac hypreal_inverse_less_swap 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_inverse_gt_0]));
qed "hypreal_inverse_less_iff";

Goal "[| 0 < z; x < y |] ==> x * inverse z < y * inverse (z::hypreal)";
by (blast_tac (claset() addSIs [hypreal_mult_less_mono1,
                                hypreal_inverse_gt_0]) 1);
qed "hypreal_mult_inverse_less_mono1";

Goal "[| 0 < z; x < y |] ==> inverse z * x < inverse (z::hypreal) * y";
by (blast_tac (claset() addSIs [hypreal_mult_less_mono2,
                                hypreal_inverse_gt_0]) 1);
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
by (forw_inst_tac [("y","r")] order_less_trans 1);
by (dres_inst_tac [("z","ra"),("x","r")] hypreal_mult_less_mono1 2);
by (dres_inst_tac [("z","x"),("x","ra")] hypreal_mult_less_mono2 3);
by (auto_tac (claset() addIs [order_less_trans], simpset()));
qed "hypreal_mult_less_gt_zero"; 

Goal "[| 0 < r; (0::hypreal) < ra; r <= x; ra <= y |] ==> r*ra <= x*y";
by (REPEAT(dtac order_le_imp_less_or_eq 1));
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
qed "hypreal_0_less_mult_iff";

Goal "((0::hypreal) <= x*y) = (0 <= x & 0 <= y | x <= 0 & y <= 0)";
by (auto_tac (claset() addDs [hypreal_mult_zero_disj],
              simpset() addsimps [order_le_less, linorder_not_less,
                                  hypreal_0_less_mult_iff]));
qed "hypreal_0_le_mult_iff";

Goal "(x*y < (0::hypreal)) = (0 < x & y < 0 | x < 0 & 0 < y)";
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_0_le_mult_iff, 
                                  linorder_not_le RS sym]));
by (auto_tac (claset() addDs [order_less_not_sym],  
              simpset() addsimps [linorder_not_le]));
qed "hypreal_mult_less_0_iff";

Goal "(x*y <= (0::hypreal)) = (0 <= x & y <= 0 | x <= 0 & 0 <= y)";
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [hypreal_0_less_mult_iff, 
                                  linorder_not_less RS sym]));
qed "hypreal_mult_le_0_iff";

Goal "[| (0::hypreal) < x; y < 0 |] ==> y*x < 0";
by (auto_tac (claset(),simpset() addsimps [hypreal_mult_commute,
    hypreal_mult_less_zero]));
qed "hypreal_mult_less_zero2";
