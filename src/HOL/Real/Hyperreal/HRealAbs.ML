(*  Title       : HRealAbs.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the hyperreals
                  Similar to RealAbs.thy
*) 

(*------------------------------------------------------------
  absolute value on hyperreals as pointwise operation on 
  equivalence class representative
 ------------------------------------------------------------*)

Goalw [hrabs_def]
     "abs (Abs_hypreal (hyprel ^^ {X})) = \
\     Abs_hypreal(hyprel ^^ {%n. abs (X n)})";
by (auto_tac (claset(),
           simpset() addsimps [hypreal_zero_def, hypreal_le,hypreal_minus]));
by (ALLGOALS(Ultra_tac THEN' arith_tac ));
qed "hypreal_hrabs";

(*------------------------------------------------------------
   Properties of the absolute value function over the reals
   (adapted version of previously proved theorems about abs)
 ------------------------------------------------------------*)

Goal "abs (0::hypreal) = 0";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_zero";
Addsimps [hrabs_zero];

Goal "(0::hypreal)<=x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_eqI1";

Goal "(0::hypreal)<x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [hypreal_less_imp_le, hrabs_eqI1]) 1);
qed "hrabs_eqI2";

Goal "x<(0::hypreal) ==> abs x = -x";
by (asm_simp_tac (simpset() addsimps [hypreal_le_def, hrabs_def]) 1); 
qed "hrabs_minus_eqI2";

Goal "x<=(0::hypreal) ==> abs x = -x";
by (auto_tac (claset() addDs [order_antisym], simpset() addsimps [hrabs_def])); 
qed "hrabs_minus_eqI1";

Goal "(0::hypreal)<= abs x";
by (auto_tac (claset() addDs [hypreal_minus_zero_less_iff RS iffD2, 
                              hypreal_less_asym], 
              simpset() addsimps [hypreal_le_def, hrabs_def]));
qed "hrabs_ge_zero";

Goal "abs(abs x) = abs (x::hypreal)";
by (auto_tac (claset() addDs [hypreal_minus_zero_less_iff RS iffD2, 
                              hypreal_less_asym], 
              simpset() addsimps [hypreal_le_def, hrabs_def]));
qed "hrabs_idempotent";
Addsimps [hrabs_idempotent];

Goalw [hrabs_def] "(abs x = (0::hypreal)) = (x=0)";
by (Simp_tac 1);
qed "hrabs_zero_iff";
AddIffs [hrabs_zero_iff];

Goalw [hrabs_def] "(x::hypreal) <= abs x";
by (auto_tac (claset() addDs [not_hypreal_leE RS hypreal_less_imp_le],
              simpset() addsimps [hypreal_le_zero_iff]));
qed "hrabs_ge_self";

Goalw [hrabs_def] "-(x::hypreal) <= abs x";
by (full_simp_tac (simpset() addsimps [hypreal_ge_zero_iff]) 1);
qed "hrabs_ge_minus_self";

(* very short proof by "transfer" *)
Goal "abs(x*(y::hypreal)) = (abs x)*(abs y)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_hrabs, hypreal_mult,abs_mult]));
qed "hrabs_mult";

Goal "abs(inverse(x)) = inverse(abs(x::hypreal))";
by (hypreal_div_undefined_case_tac "x=0" 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
       simpset() addsimps [hypreal_hrabs,
                           hypreal_inverse,hypreal_zero_def]));
by (ultra_tac (claset(), simpset() addsimps [abs_inverse]) 1);
qed "hrabs_inverse";

Goal "abs(x+(y::hypreal)) <= abs x + abs y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), 
      simpset() addsimps [hypreal_hrabs, hypreal_add,hypreal_le,
                        abs_triangle_ineq]));
qed "hrabs_triangle_ineq";

Goal "abs((w::hypreal) + x + y) <= abs(w) + abs(x) + abs(y)";
by (auto_tac (claset() addSIs [hrabs_triangle_ineq RS hypreal_le_trans,
                               hypreal_add_left_le_mono1],
    simpset() addsimps [hypreal_add_assoc]));
qed "hrabs_triangle_ineq_three";

Goalw [hrabs_def] "abs(-x)=abs((x::hypreal))";
by (auto_tac (claset() addSDs [not_hypreal_leE, hypreal_less_asym] 
                       addIs [hypreal_le_anti_sym],
              simpset() addsimps [hypreal_ge_zero_iff]));
qed "hrabs_minus_cancel";
Addsimps [hrabs_minus_cancel];

val prem1::prem2::rest = goal thy 
    "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)";
by (rtac hypreal_le_less_trans 1);
by (rtac hrabs_triangle_ineq 1);
by (rtac ([prem1,prem2] MRS hypreal_add_less_mono) 1);
qed "hrabs_add_less";

val prem1::prem2::rest = 
    goal thy "[| abs x<r; abs y<s |] ==> abs(x*y)<r*(s::hypreal)";
by (simp_tac (simpset() addsimps [hrabs_mult]) 1);
by (rtac hypreal_mult_le_less_trans 1);
by (rtac hrabs_ge_zero 1);
by (rtac prem2 1);
by (rtac hypreal_mult_less_mono1 1);
by (rtac (prem2 RS (hrabs_ge_zero RS hypreal_le_less_trans)) 1);
by (rtac prem1 1);
by (rtac ([prem1 RS (hrabs_ge_zero RS hypreal_le_less_trans),
           prem2 RS (hrabs_ge_zero RS hypreal_le_less_trans)] 
          MRS hypreal_mult_order) 1);
qed "hrabs_mult_less";

Goal "1hr < abs x ==> abs y <= abs(x*y)";
by (cut_inst_tac [("x1","y")] (hrabs_ge_zero RS hypreal_le_imp_less_or_eq) 1);
by (EVERY1[etac disjE,rtac hypreal_less_imp_le]);
by (dres_inst_tac [("x1","1hr")]  (hypreal_less_minus_iff RS iffD1) 1);
by (forw_inst_tac [("y","abs x +-1hr")] hypreal_mult_order 1);
by (assume_tac 1);
by (rtac (hypreal_less_minus_iff RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_mult_distrib2,
    hrabs_mult, hypreal_mult_commute,hypreal_minus_mult_eq2 RS sym]) 1);
by (dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_le_refl,hrabs_mult]) 1);
qed "hrabs_mult_le";

Goal "[| 1hr < abs x; r < abs y|] ==> r < abs(x*y)";
by (fast_tac (HOL_cs addIs [hrabs_mult_le, hypreal_less_le_trans]) 1);
qed "hrabs_mult_gt";

Goal "abs x < r ==> (0::hypreal) < r";
by (blast_tac (claset() addSIs [hypreal_le_less_trans,
    hrabs_ge_zero]) 1);
qed "hrabs_less_gt_zero";

Goalw [hrabs_def] "abs 1hr = 1hr";
by (auto_tac (claset() addSDs [not_hypreal_leE RS hypreal_less_asym], 
      simpset() addsimps [hypreal_zero_less_one]));
qed "hrabs_one";

Goal "abs x = (x::hypreal) | abs x = -x";
by (cut_inst_tac [("x","0"),("y","x")] hypreal_linear 1);
by (fast_tac (claset() addIs [hrabs_eqI2,hrabs_minus_eqI2,
                            hrabs_zero]) 1);
qed "hrabs_disj";

Goal "abs x = (y::hypreal) ==> x = y | -x = y";
by (dtac sym 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x1","x")] (hrabs_disj RS disjE) 1);
by (REPEAT(Asm_simp_tac 1));
qed "hrabs_eq_disj";

Goal "(abs x < (r::hypreal)) = (-r < x & x < r)";
by (Step_tac 1);
by (rtac (hypreal_less_swap_iff RS iffD2) 1);
by (asm_simp_tac (simpset() addsimps [(hrabs_ge_minus_self 
    RS hypreal_le_less_trans)]) 1);
by (asm_simp_tac (simpset() addsimps [(hrabs_ge_self 
    RS hypreal_le_less_trans)]) 1);
by (EVERY1 [dtac (hypreal_less_swap_iff RS iffD1), rotate_tac 1, 
            dtac (hypreal_minus_minus RS subst), 
            cut_inst_tac [("x","x")] hrabs_disj, dtac disjE ]);
by (assume_tac 3 THEN Auto_tac);
qed "hrabs_interval_iff";

Goal "(abs x < (r::hypreal)) = (- x < r & x < r)";
by (auto_tac (claset(),  simpset() addsimps [hrabs_interval_iff]));
by (dtac (hypreal_less_swap_iff RS iffD1) 1);
by (dtac (hypreal_less_swap_iff RS iffD1) 2);
by (Auto_tac);
qed "hrabs_interval_iff2";

(* Needed in Geom.ML *)
Goal "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_hrabs, hypreal_minus,hypreal_add]));
by (Ultra_tac 1 THEN arith_tac 1);
qed "hrabs_add_lemma_disj";

(***SHOULD BE TRIVIAL GIVEN SIMPROCS
Goal "abs((x::hypreal) + -y) = abs (y + -x)";
by (rtac (hrabs_minus_cancel RS subst) 1);
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hrabs_minus_add_cancel";

(* Needed in Geom.ML *)
Goal "(x::hypreal) + - y + (z + - y) = abs (x + - z) \
\     ==> y = z | x = y";
by (rtac (hypreal_minus_eq_cancel RS subst) 1);
by (res_inst_tac [("b1","y")] (hypreal_minus_eq_cancel RS subst) 1);
by (rtac hrabs_add_lemma_disj 1);
by (asm_full_simp_tac (simpset() addsimps [hrabs_minus_add_cancel] 
         @ hypreal_add_ac) 1);
qed "hrabs_add_lemma_disj2";
***)
 
(*----------------------------------------------------------
    Relating hrabs to abs through embedding of IR into IR*
 ----------------------------------------------------------*)
Goalw [hypreal_of_real_def] 
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)";
by (auto_tac (claset(), simpset() addsimps [hypreal_hrabs]));
qed "hypreal_of_real_hrabs";
