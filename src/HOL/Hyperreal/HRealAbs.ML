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
     "abs (number_of v :: hypreal) = \
\       (if neg (number_of v) then number_of (bin_minus v) \
\        else number_of v)";
by (Simp_tac 1); 
qed "hrabs_number_of";
Addsimps [hrabs_number_of];

Goalw [hrabs_def]
     "abs (Abs_hypreal (hyprel `` {X})) = \
\     Abs_hypreal(hyprel `` {%n. abs (X n)})";
by (auto_tac (claset(),
              simpset_of HyperDef.thy 
                  addsimps [hypreal_zero_def, hypreal_le,hypreal_minus]));
by (ALLGOALS(Ultra_tac THEN' arith_tac ));
qed "hypreal_hrabs";

(*------------------------------------------------------------
   Properties of the absolute value function over the reals
   (adapted version of previously proved theorems about abs)
 ------------------------------------------------------------*)

Goal "abs (#0::hypreal) = #0";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_zero";
Addsimps [hrabs_zero];

Goal "(#0::hypreal)<=x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_eqI1";

Goal "(#0::hypreal)<x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [order_less_imp_le, hrabs_eqI1]) 1);
qed "hrabs_eqI2";

Goal "x<(#0::hypreal) ==> abs x = -x";
by (asm_simp_tac (simpset() addsimps [hypreal_le_def, hrabs_def]) 1); 
qed "hrabs_minus_eqI2";

Goal "x<=(#0::hypreal) ==> abs x = -x";
by (auto_tac (claset() addDs [order_antisym], simpset() addsimps [hrabs_def])); 
qed "hrabs_minus_eqI1";

Goal "(#0::hypreal)<= abs x";
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

Goalw [hrabs_def] "(abs x = (#0::hypreal)) = (x=#0)";
by (Simp_tac 1);
qed "hrabs_zero_iff";
AddIffs [hrabs_zero_iff];

Goalw [hrabs_def] "(x::hypreal) <= abs x";
by (auto_tac (claset() addDs [not_hypreal_leE, order_less_imp_le],
              simpset() addsimps [hypreal_le_zero_iff RS sym]));
qed "hrabs_ge_self";

Goalw [hrabs_def] "-(x::hypreal) <= abs x";
by (simp_tac (simpset() addsimps [hypreal_ge_zero_iff]) 1);
qed "hrabs_ge_minus_self";

(* very short proof by "transfer" *)
Goal "abs(x*(y::hypreal)) = (abs x)*(abs y)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_hrabs, hypreal_mult,abs_mult]));
qed "hrabs_mult";
Addsimps [hrabs_mult];

Goal "abs(inverse(x)) = inverse(abs(x::hypreal))";
by (hypreal_div_undefined_case_tac "x=#0" 1);
by (simp_tac (simpset() addsimps [HYPREAL_DIVIDE_ZERO]) 1); 
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
by (auto_tac (claset() addSIs [hrabs_triangle_ineq RS order_trans,
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
by (rtac order_le_less_trans 1);
by (rtac hrabs_triangle_ineq 1);
by (rtac ([prem1,prem2] MRS hypreal_add_less_mono) 1);
qed "hrabs_add_less";

Goal "[| abs x<r;  abs y<s |] ==> abs x * abs y < r * (s::hypreal)";
by (subgoal_tac "#0 < r" 1);
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 2); 
by (case_tac "y = #0" 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_0_less_mult_iff]) 1); 
by (rtac hypreal_mult_less_mono 1); 
by (auto_tac (claset(), 
              simpset() addsimps [hrabs_def, linorder_neq_iff] 
                        addsplits [split_if_asm])); 
qed "hrabs_mult_less";

Goal "((#0::hypreal) < abs x) = (x ~= 0)";
by (simp_tac (simpset() addsimps [hrabs_def]) 1);
by (arith_tac 1);
qed "hypreal_0_less_abs_iff";
Addsimps [hypreal_0_less_abs_iff];

Goal "abs x < r ==> (#0::hypreal) < r";
by (blast_tac (claset() addSIs [order_le_less_trans, hrabs_ge_zero]) 1);
qed "hrabs_less_gt_zero";

Goal "abs x = (x::hypreal) | abs x = -x";
by (cut_inst_tac [("x","#0"),("y","x")] hypreal_linear 1);
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
    RS order_le_less_trans)]) 1);
by (asm_simp_tac (simpset() addsimps [(hrabs_ge_self 
    RS order_le_less_trans)]) 1);
by (EVERY1 [dtac (hypreal_less_swap_iff RS iffD1), rotate_tac 1, 
            dtac (hypreal_minus_minus RS subst), 
            cut_inst_tac [("x","x")] hrabs_disj, dtac disjE ]);
by (assume_tac 3 THEN Auto_tac);
qed "hrabs_interval_iff";

Goal "(abs x < (r::hypreal)) = (- x < r & x < r)";
by (auto_tac (claset(),  simpset() addsimps [hrabs_interval_iff]));
qed "hrabs_interval_iff2";


(* Needed in Geom.ML *)
Goal "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_add_lemma_disj";

Goal "abs((x::hypreal) + -y) = abs (y + -x)";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_minus_add_cancel";

(* Needed in Geom.ML?? *)
Goal "(x::hypreal) + - y + (z + - y) = abs (x + - z) ==> y = z | x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_add_lemma_disj2";

 
(*----------------------------------------------------------
    Relating hrabs to abs through embedding of IR into IR*
 ----------------------------------------------------------*)
Goalw [hypreal_of_real_def] 
    "abs (hypreal_of_real r) = hypreal_of_real (abs r)";
by (auto_tac (claset(), simpset() addsimps [hypreal_hrabs]));
qed "hypreal_of_real_hrabs";


(*----------------------------------------------------------------------------
             Embedding of the naturals in the hyperreals
 ----------------------------------------------------------------------------*)

Goal "hypreal_of_nat (m + n) = hypreal_of_nat m + hypreal_of_nat n";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_add";
Addsimps [hypreal_of_nat_add];

Goal "hypreal_of_nat (m * n) = hypreal_of_nat m * hypreal_of_nat n";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_mult";
Addsimps [hypreal_of_nat_mult];

Goalw [hypreal_of_nat_def] 
      "(n < m) = (hypreal_of_nat n < hypreal_of_nat m)";
by (auto_tac (claset() addIs [hypreal_add_less_mono1], simpset()));
qed "hypreal_of_nat_less_iff";
Addsimps [hypreal_of_nat_less_iff RS sym];

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

Goalw [hypreal_of_nat_def, hypreal_of_real_def, real_of_nat_def] 
     "hypreal_of_nat  m = Abs_hypreal(hyprel``{%n. real m})";
by Auto_tac;
qed "hypreal_of_nat_iff";

Goal "inj hypreal_of_nat";
by (simp_tac (simpset() addsimps [inj_on_def, hypreal_of_nat_def]) 1);
qed "inj_hypreal_of_nat";

Goalw [hypreal_of_nat_def] 
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + 1hr";
by (simp_tac (simpset() addsimps [real_of_nat_Suc]) 1);
qed "hypreal_of_nat_Suc";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "hypreal_of_nat (number_of v :: nat) = \
\        (if neg (number_of v) then #0 \
\         else (number_of v :: hypreal))";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_number_of";
Addsimps [hypreal_of_nat_number_of];

Goal "hypreal_of_nat 0 = #0";
by (simp_tac (simpset() delsimps [numeral_0_eq_0]
			addsimps [numeral_0_eq_0 RS sym]) 1);
qed "hypreal_of_nat_zero";
Addsimps [hypreal_of_nat_zero];
