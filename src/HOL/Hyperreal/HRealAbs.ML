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

(*------------------------------------------------------------
   Properties of the absolute value function over the reals
   (adapted version of previously proved theorems about abs)
 ------------------------------------------------------------*)

Goal "abs (0::hypreal) = 0";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_zero";
Addsimps [hrabs_zero];

Goal "abs (1::hypreal) = 1";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_one";
Addsimps [hrabs_one];

Goal "(0::hypreal)<=x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_eqI1";

Goal "(0::hypreal)<x ==> abs x = x";
by (asm_simp_tac (simpset() addsimps [order_less_imp_le, hrabs_eqI1]) 1);
qed "hrabs_eqI2";

Goal "x<(0::hypreal) ==> abs x = -x";
by (asm_simp_tac (simpset() addsimps [hypreal_le_def, hrabs_def]) 1); 
qed "hrabs_minus_eqI2";

Goal "x<=(0::hypreal) ==> abs x = -x";
by (auto_tac (claset() addDs [order_antisym], simpset() addsimps [hrabs_def]));qed "hrabs_minus_eqI1";

Goal "(0::hypreal)<= abs x";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_ge_zero";

Goal "abs(abs x) = abs (x::hypreal)";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_idempotent";
Addsimps [hrabs_idempotent];

Goalw [hrabs_def] "(abs x = (0::hypreal)) = (x=0)";
by (Simp_tac 1);
qed "hrabs_zero_iff";
AddIffs [hrabs_zero_iff];

Goalw [hrabs_def] "(x::hypreal) <= abs x";
by (Simp_tac 1); 
qed "hrabs_ge_self";

Goalw [hrabs_def] "-(x::hypreal) <= abs x";
by (Simp_tac 1);
qed "hrabs_ge_minus_self";

(* proof by "transfer" *)
Goal "abs(x*(y::hypreal)) = (abs x)*(abs y)";  
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_hrabs, hypreal_mult,abs_mult]));
qed "hrabs_mult";
Addsimps [hrabs_mult];

Goal "abs(inverse(x)) = inverse(abs(x::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_minus_inverse, hrabs_def]) 1);  
qed "hrabs_inverse";

Goalw [hrabs_def] "abs(x+(y::hypreal)) <= abs x + abs y"; 
by (Simp_tac 1);
qed "hrabs_triangle_ineq";

Goal "abs((w::hypreal) + x + y) <= abs(w) + abs(x) + abs(y)";
by (simp_tac (simpset() addsimps [hrabs_triangle_ineq RS order_trans]) 1);
qed "hrabs_triangle_ineq_three";

Goalw [hrabs_def] "abs(-x) = abs((x::hypreal))";
by (Simp_tac 1);
qed "hrabs_minus_cancel";
Addsimps [hrabs_minus_cancel];

Goalw [hrabs_def] "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)";
by (asm_full_simp_tac (simpset() addsplits [split_if_asm]) 1); 
qed "hrabs_add_less";

Goal "[| abs x<r;  abs y<s |] ==> abs x * abs y < r * (s::hypreal)";
by (subgoal_tac "0 < r" 1);
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 2); 
by (case_tac "y = 0" 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_0_less_mult_iff]) 1); 
by (rtac hypreal_mult_less_mono 1); 
by (auto_tac (claset(), 
              simpset() addsimps [hrabs_def, linorder_neq_iff] 
                        addsplits [split_if_asm])); 
qed "hrabs_mult_less";

Goal "((0::hypreal) < abs x) = (x ~= 0)";
by (simp_tac (simpset() addsimps [hrabs_def]) 1);
by (arith_tac 1);
qed "hypreal_0_less_abs_iff";
Addsimps [hypreal_0_less_abs_iff];

Goal "abs x < r ==> (0::hypreal) < r";
by (blast_tac (claset() addSIs [order_le_less_trans, hrabs_ge_zero]) 1);
qed "hrabs_less_gt_zero";

Goal "abs x = (x::hypreal) | abs x = -x";
by (simp_tac (simpset() addsimps [hrabs_def]) 1); 
qed "hrabs_disj";

Goal "abs x = (y::hypreal) ==> x = y | -x = y";
by (asm_full_simp_tac (simpset() addsimps [hrabs_def] 
                                 addsplits [split_if_asm]) 1); 
qed "hrabs_eq_disj";

Goalw [hrabs_def] "(abs x < (r::hypreal)) = (-r < x & x < r)";
by Auto_tac; 
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
     "hypreal_of_nat (Suc n) = hypreal_of_nat n + (1::hypreal)";
by (simp_tac (simpset() addsimps [real_of_nat_Suc]) 1);
qed "hypreal_of_nat_Suc";

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "hypreal_of_nat (number_of v :: nat) = \
\        (if neg (number_of v) then 0 \
\         else (number_of v :: hypreal))";
by (simp_tac (simpset() addsimps [hypreal_of_nat_def]) 1);
qed "hypreal_of_nat_number_of";
Addsimps [hypreal_of_nat_number_of];

Goal "hypreal_of_nat 0 = 0";
by (simp_tac (simpset() delsimps [numeral_0_eq_0]
                        addsimps [numeral_0_eq_0 RS sym]) 1);
qed "hypreal_of_nat_zero";
Addsimps [hypreal_of_nat_zero];

Goal "hypreal_of_nat 1 = 1";
by (simp_tac (simpset() addsimps [hypreal_of_nat_Suc]) 1); 
qed "hypreal_of_nat_one";
Addsimps [hypreal_of_nat_one];
