(*  Title       : RealAbs.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the reals
*) 


(** abs (absolute value) **)

Goalw [abs_real_def]
     "abs (number_of v :: real) = \
\       (if neg (number_of v) then number_of (bin_minus v) \
\        else number_of v)";
by (simp_tac
    (simpset () addsimps
      bin_arith_simps@
      [minus_real_number_of, zero_eq_numeral_0, le_real_number_of_eq_not_less,
       less_real_number_of, real_of_int_le_iff]) 1);
qed "abs_nat_number_of";

Addsimps [abs_nat_number_of];

Goalw [abs_real_def]
  "P(abs (x::real)) = ((#0 <= x --> P x) & (x < #0 --> P(-x)))";
by(auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_split";


(*----------------------------------------------------------------------------
       Properties of the absolute value function over the reals
       (adapted version of previously proved theorems about abs)
 ----------------------------------------------------------------------------*)

Goalw [abs_real_def] "abs (r::real) = (if #0<=r then r else -r)";
by Auto_tac;
qed "abs_iff";

Goalw [abs_real_def] "abs #0 = (#0::real)";
by Auto_tac;
qed "abs_zero";
Addsimps [abs_zero];

Goalw [abs_real_def] "abs (#0::real) = -#0";
by (Simp_tac 1);
qed "abs_minus_zero";

Goalw [abs_real_def] "(#0::real)<=x ==> abs x = x";
by (Asm_simp_tac 1);
qed "abs_eqI1";

Goalw [abs_real_def] "(#0::real)<x ==> abs x = x";
by (Asm_simp_tac 1);
qed "abs_eqI2";

Goalw [abs_real_def,real_le_def] "x<(#0::real) ==> abs x = -x";
by (Asm_simp_tac 1);
qed "abs_minus_eqI2";

Goalw [abs_real_def] "x<=(#0::real) ==> abs x = -x";
by (Asm_simp_tac 1);
qed "abs_minus_eqI1";

Goalw [abs_real_def] "(#0::real)<= abs x";
by (Simp_tac 1);
qed "abs_ge_zero";

Goalw [abs_real_def] "abs(abs x)=abs (x::real)";
by (Simp_tac 1);
qed "abs_idempotent";
Addsimps [abs_idempotent];

Goalw [abs_real_def] "(abs x = #0) = (x=(#0::real))";
by (Full_simp_tac 1);
qed "abs_zero_iff";
AddIffs [abs_zero_iff];

Goalw [abs_real_def] "x<=abs (x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_ge_self";

Goalw [abs_real_def] "-x<=abs (x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_ge_minus_self";

Goalw [abs_real_def] "abs (x * y) = abs x * abs (y::real)";
by (auto_tac (claset() addSDs [order_antisym],
	      simpset() addsimps [real_0_le_mult_iff]));
qed "abs_mult";

Goalw [abs_real_def] "abs(inverse(x::real)) = inverse(abs(x))";
by (real_div_undefined_case_tac "x=0" 1);
by (auto_tac (claset(), 
              simpset() addsimps [real_minus_inverse, real_le_less] @ 
	          (map rename_numerals [INVERSE_ZERO, real_inverse_gt_zero])));
qed "abs_inverse";

Goal "abs (x * inverse y) = (abs x) * inverse (abs (y::real))";
by (asm_simp_tac (simpset() addsimps [abs_mult, abs_inverse]) 1);
qed "abs_mult_inverse";

Goalw [abs_real_def] "abs(x+y) <= abs x + abs (y::real)";
by (Simp_tac 1);
qed "abs_triangle_ineq";

(*Unused, but perhaps interesting as an example*)
Goal "abs(w + x + y + z) <= abs(w) + abs(x) + abs(y) + abs(z::real)";
by (simp_tac (simpset() addsimps [abs_triangle_ineq RS order_trans]) 1);
qed "abs_triangle_ineq_four";

Goalw [abs_real_def] "abs(-x)=abs(x::real)";
by (Simp_tac 1);
qed "abs_minus_cancel";

Goalw [abs_real_def] "abs(x + (-y)) = abs (y + (-(x::real)))";
by (Simp_tac 1);
qed "abs_minus_add_cancel";

Goalw [abs_real_def] "abs(x + (-y)) <= abs x + abs (y::real)";
by (Simp_tac 1);
qed "abs_triangle_minus_ineq";

Goalw [abs_real_def] "abs x < r --> abs y < s --> abs(x+y) < r+(s::real)";
by (Simp_tac 1);
qed_spec_mp "abs_add_less";

Goalw [abs_real_def] "abs x < r --> abs y < s --> abs(x+ (-y)) < r+(s::real)";
by (Simp_tac 1);
qed "abs_add_minus_less";

(* lemmas manipulating terms *)
Goal "((#0::real)*x<r)=(#0<r)";
by (Simp_tac 1);
qed "real_mult_0_less";

Goal "[| (#0::real)<y; x<r; y*r<t*s |] ==> y*x<t*s";
by (blast_tac (claset() addSIs [rename_numerals real_mult_less_mono2] 
                        addIs  [real_less_trans]) 1);
qed "real_mult_less_trans";

Goal "[| (#0::real)<=y; x<r; y*r<t*s; #0<t*s|] ==> y*x<t*s";
by (dtac real_le_imp_less_or_eq 1);
by (fast_tac (HOL_cs addEs [real_mult_0_less RS iffD2,
			    real_mult_less_trans]) 1);
qed "real_mult_le_less_trans";

Goal "[| abs x<r; abs y<s |] ==> abs(x*y)<r*(s::real)";
by (simp_tac (simpset() addsimps [abs_mult]) 1);
by (rtac real_mult_le_less_trans 1);
by (rtac abs_ge_zero 1);
by (assume_tac 1);
by (rtac (rename_numerals real_mult_order) 2);
by (auto_tac (claset() addSIs [real_mult_less_mono1,
    abs_ge_zero] addIs [real_le_less_trans],simpset()));
qed "abs_mult_less";

Goal "[| abs x < r; abs y < s |] ==> abs(x)*abs(y)<r*(s::real)";
by (auto_tac (claset() addIs [abs_mult_less],
              simpset() addsimps [abs_mult RS sym]));
qed "abs_mult_less2";

Goal "(#1::real) < abs x ==> abs y <= abs(x*y)";
by (cut_inst_tac [("x1","y")] (abs_ge_zero RS real_le_imp_less_or_eq) 1);
by (EVERY1[etac disjE,rtac real_less_imp_le]);
by (dres_inst_tac [("W","#1")]  real_less_sum_gt_zero 1);
by (forw_inst_tac [("y","abs x + (-#1)")] 
    (rename_numerals real_mult_order) 1);
by (rtac real_sum_gt_zero_less 2);
by (asm_full_simp_tac (simpset() 
    addsimps [real_add_mult_distrib2,
    real_mult_commute, abs_mult]) 2);
by (dtac sym 2);
by (auto_tac (claset(),simpset() addsimps [abs_mult]));
qed "abs_mult_le";

Goal "[| (#1::real) < abs x; r < abs y|] ==> r < abs(x*y)";
by (blast_tac (HOL_cs addIs [abs_mult_le, real_less_le_trans]) 1);
qed "abs_mult_gt";

Goal "abs(x)<r ==> (#0::real)<r";
by (blast_tac (claset() addSIs [real_le_less_trans,abs_ge_zero]) 1);
qed "abs_less_gt_zero";

Goalw [abs_real_def] "abs #1 = (#1::real)";
by (Simp_tac 1);
qed "abs_one";

Goalw [abs_real_def] "abs (-#1) = (#1::real)";
by (Simp_tac 1);
qed "abs_minus_one";
Addsimps [abs_minus_one];

Goalw [abs_real_def] "abs x =x | abs x = -(x::real)";
by Auto_tac;
qed "abs_disj";

Goalw [abs_real_def] "(abs x < r) = (-r<x & x<(r::real))";
by Auto_tac;
qed "abs_interval_iff";

Goalw [abs_real_def] "(abs x <= r) = (-r<=x & x<=(r::real))";
by Auto_tac;
qed "abs_le_interval_iff";

Goalw [abs_real_def] "(abs (x + (-y)) < r) = (y + (-r) < x & x < y + (r::real))";
by Auto_tac;
qed "abs_add_minus_interval_iff";

Goalw [abs_real_def] "(#0::real) < k ==> #0 < k + abs(x)";
by Auto_tac;
qed "abs_add_pos_gt_zero";

Goalw [abs_real_def] "(#0::real) < #1 + abs(x)";
by Auto_tac;
qed "abs_add_one_gt_zero";
Addsimps [abs_add_one_gt_zero];

(* 05/2000 *)
Goalw [abs_real_def] "~ abs x < (#0::real)";
by Auto_tac;
qed "abs_not_less_zero";
Addsimps [abs_not_less_zero];

Goal "abs h < abs y - abs x ==> abs (x + h) < abs (y::real)";
by (auto_tac (claset() addIs [abs_triangle_ineq RS real_le_less_trans], 
    simpset()));
qed "abs_circle";

Goalw [abs_real_def] "(abs x <= (#0::real)) = (x = #0)";
by Auto_tac;
qed "abs_le_zero_iff";
Addsimps [abs_le_zero_iff];

Goal "((#0::real) < abs x) = (x ~= 0)";
by (simp_tac (simpset() addsimps [abs_real_def]) 1);
by (arith_tac 1);
qed "real_0_less_abs_iff";
Addsimps [real_0_less_abs_iff];

Goal "abs (real_of_nat x) = real_of_nat x";
by (auto_tac (claset() addIs [abs_eqI1],simpset()
    addsimps [rename_numerals real_of_nat_ge_zero]));
qed "abs_real_of_nat_cancel";
Addsimps [abs_real_of_nat_cancel];

Goal "~ abs(x) + (#1::real) < x";
by (rtac real_leD 1);
by (auto_tac (claset() addIs [abs_ge_self RS real_le_trans],simpset()));
qed "abs_add_one_not_less_self";
Addsimps [abs_add_one_not_less_self];

(* used in vector theory *)
Goal "abs(w + x + (y::real)) <= abs(w) + abs(x) + abs(y)";
by (auto_tac (claset() addSIs [(abs_triangle_ineq 
    RS real_le_trans),real_add_left_le_mono1],
    simpset() addsimps [real_add_assoc]));
qed "abs_triangle_ineq_three";

Goalw [abs_real_def] "abs(x - y) < y ==> (#0::real) < y";
by (case_tac "#0 <= x - y" 1);
by (Auto_tac);
qed "abs_diff_less_imp_gt_zero";

Goalw [abs_real_def] "abs(x - y) < x ==> (#0::real) < x";
by (case_tac "#0 <= x - y" 1);
by (Auto_tac);
qed "abs_diff_less_imp_gt_zero2";

Goal "abs(x - y) < y ==> (#0::real) < x";
by (auto_tac (claset(),simpset() addsimps [abs_interval_iff]));
qed "abs_diff_less_imp_gt_zero3";

Goal "abs(x - y) < -y ==> x < (#0::real)";
by (auto_tac (claset(),simpset() addsimps [abs_interval_iff]));
qed "abs_diff_less_imp_gt_zero4";

Goalw [abs_real_def] 
     " abs(x) <= abs(x + (-y)) + abs((y::real))";
by Auto_tac;
qed "abs_triangle_ineq_minus_cancel";

Goal "abs ((x::real) + y + (-l + -m)) <= abs(x + -l) + abs(y + -m)";
by (full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (res_inst_tac [("x1","y")] (real_add_left_commute RS ssubst) 1);
by (rtac (real_add_assoc RS subst) 1);
by (rtac abs_triangle_ineq 1);
qed "abs_sum_triangle_ineq";
