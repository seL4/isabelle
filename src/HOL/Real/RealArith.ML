(*  Title:      HOL/Real/RealArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Assorted facts that need binary literals and the arithmetic decision procedure

Also, common factor cancellation
*)

(** Division and inverse **)

Goal "((#0::real) < inverse x) = (#0 < x)";
by (case_tac "x=#0" 1);
by (asm_simp_tac (HOL_ss addsimps [rename_numerals INVERSE_ZERO]) 1); 
by (auto_tac (claset() addDs [rename_numerals real_inverse_less_zero], 
              simpset() addsimps [linorder_neq_iff, 
                                  rename_numerals real_inverse_gt_zero]));  
qed "real_0_less_inverse_iff";
AddIffs [real_0_less_inverse_iff];

Goal "(inverse x < (#0::real)) = (x < #0)";
by (case_tac "x=#0" 1);
by (asm_simp_tac (HOL_ss addsimps [rename_numerals INVERSE_ZERO]) 1); 
by (auto_tac (claset() addDs [rename_numerals real_inverse_less_zero], 
              simpset() addsimps [linorder_neq_iff, 
                                  rename_numerals real_inverse_gt_zero]));  
qed "real_inverse_less_0_iff";
AddIffs [real_inverse_less_0_iff];

Goal "((#0::real) <= inverse x) = (#0 <= x)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
qed "real_0_le_inverse_iff";
AddIffs [real_0_le_inverse_iff];

Goal "(inverse x <= (#0::real)) = (x <= #0)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
qed "real_inverse_le_0_iff";
AddIffs [real_inverse_le_0_iff];

Goalw [real_divide_def] "x/(#0::real) = #0";
by (stac (rename_numerals INVERSE_ZERO) 1); 
by (Simp_tac 1); 
qed "REAL_DIVIDE_ZERO";

(*generalize?*)
Goal "((#0::real) < #1/x) = (#0 < x)";
by (simp_tac (simpset() addsimps [real_divide_def]) 1);
qed "real_0_less_recip_iff";
AddIffs [real_0_less_recip_iff];

Goal "(#1/x < (#0::real)) = (x < #0)";
by (simp_tac (simpset() addsimps [real_divide_def]) 1);
qed "real_recip_less_0_iff";
AddIffs [real_recip_less_0_iff];

Goal "inverse (x::real) = #1/x";
by (simp_tac (simpset() addsimps [real_divide_def]) 1); 
qed "real_inverse_eq_divide";

Goal "(x::real)/#1 = x";
by (simp_tac (simpset() addsimps [real_divide_def]) 1); 
qed "real_divide_1";
Addsimps [real_divide_1];


(**** Factor cancellation theorems for "real" ****)

(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

bind_thm ("real_mult_minus_right", real_minus_mult_eq2 RS sym);

Goal "(-y < -x) = ((x::real) < y)";
by (arith_tac 1);
qed "real_minus_less_minus";

Goal "[| i<j;  k < (0::real) |] ==> j*k < i*k";
by (rtac (real_minus_less_minus RS iffD1) 1);
by (auto_tac (claset(), 
              simpset() delsimps [real_minus_mult_eq2 RS sym]
                        addsimps [real_minus_mult_eq2])); 
qed "real_mult_less_mono1_neg";

Goal "[| i<j;  k < (0::real) |] ==> k*j < k*i";
by (rtac (real_minus_less_minus RS iffD1) 1);
by (auto_tac (claset(), 
              simpset() delsimps [real_minus_mult_eq1 RS sym]
                            addsimps [real_minus_mult_eq1]));;
qed "real_mult_less_mono2_neg";

Goal "[| i <= j;  (0::real) <= k |] ==> i*k <= j*k";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, real_mult_less_mono1]));  
qed "real_mult_le_mono1";

Goal "[| i <= j;  k <= (0::real) |] ==> j*k <= i*k";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, real_mult_less_mono1_neg]));  
qed "real_mult_le_mono1_neg";

Goal "[| i <= j;  (0::real) <= k |] ==> k*i <= k*j";
by (dtac real_mult_le_mono1 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [real_mult_commute])));
qed "real_mult_le_mono2";

Goal "[| i <= j;  k <= (0::real) |] ==> k*j <= k*i";
by (dtac real_mult_le_mono1_neg 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [real_mult_commute])));
qed "real_mult_le_mono2_neg";

Goal "(m*k < n*k) = (((#0::real) < k & m<n) | (k < #0 & n<m))";
by (case_tac "k = (0::real)" 1);
by (auto_tac (claset(), 
              simpset() addsimps [linorder_neq_iff, 
                          real_mult_less_mono1, real_mult_less_mono1_neg]));  
by (auto_tac (claset(), 
              simpset() addsimps [linorder_not_less,
				  inst "y1" "m*k" (linorder_not_le RS sym),
                                  inst "y1" "m" (linorder_not_le RS sym)]));
by (TRYALL (etac notE));
by (auto_tac (claset(), 
              simpset() addsimps [order_less_imp_le, real_mult_le_mono1,
                                            real_mult_le_mono1_neg]));  
qed "real_mult_less_cancel2";

Goal "(m*k <= n*k) = (((#0::real) < k --> m<=n) & (k < #0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  real_mult_less_cancel2]) 1);
qed "real_mult_le_cancel2";

Goal "(k*m < k*n) = (((#0::real) < k & m<n) | (k < #0 & n<m))";
by (simp_tac (simpset() addsimps [inst "z" "k" real_mult_commute, 
                                  real_mult_less_cancel2]) 1);
qed "real_mult_less_cancel1";

Goal "!!k::real. (k*m <= k*n) = ((#0 < k --> m<=n) & (k < #0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  real_mult_less_cancel1]) 1);
qed "real_mult_le_cancel1";

Goal "!!k::real. (k*m = k*n) = (k = #0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [real_mult_left_cancel]));  
qed "real_mult_eq_cancel1";

Goal "!!k::real. (m*k = n*k) = (k = #0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [real_mult_right_cancel]));  
qed "real_mult_eq_cancel2";

Goal "!!k::real. k~=#0 ==> (k*m) / (k*n) = (m/n)";
by (asm_simp_tac
    (simpset() addsimps [real_divide_def, real_inverse_distrib]) 1); 
by (subgoal_tac "k * m * (inverse k * inverse n) = \
\                (k * inverse k) * (m * inverse n)" 1);
by (asm_full_simp_tac (simpset() addsimps []) 1); 
by (asm_full_simp_tac (HOL_ss addsimps real_mult_ac) 1); 
qed "real_mult_div_cancel1";


local
  open Real_Numeral_Simprocs
in

val rel_real_number_of = [eq_real_number_of, less_real_number_of, 
                          le_real_number_of_eq_not_less];

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_plus_1s))
            THEN ALLGOALS
                 (simp_tac 
                  (HOL_ss addsimps [eq_real_number_of, 
                                    real_mult_minus_right RS sym]@
    [mult_real_number_of, real_mult_number_of_left]@bin_simps@real_mult_ac))
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (HOL_ss addsimps rel_real_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "realdiv_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" HOLogic.realT
  val cancel = real_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "realeq_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val cancel = real_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "realless_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.realT
  val cancel = real_mult_less_cancel1 RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "realle_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.realT
  val cancel = real_mult_le_cancel1 RS trans
  val neg_exchanges = true
)

val real_cancel_numeral_factors = 
  map prep_simproc
   [("realeq_cancel_numeral_factors",
     prep_pats ["(l::real) * m = n", "(l::real) = m * n"], 
     EqCancelNumeralFactor.proc),
    ("realless_cancel_numeral_factors", 
     prep_pats ["(l::real) * m < n", "(l::real) < m * n"], 
     LessCancelNumeralFactor.proc),
    ("realle_cancel_numeral_factors", 
     prep_pats ["(l::real) * m <= n", "(l::real) <= m * n"], 
     LeCancelNumeralFactor.proc),
    ("realdiv_cancel_numeral_factors", 
     prep_pats ["((l::real) * m) / n", "(l::real) / (m * n)"], 
     DivCancelNumeralFactor.proc)];

end;

Addsimprocs real_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 

test "#0 <= (y::real) * #-2";
test "#9*x = #12 * (y::real)";
test "(#9*x) / (#12 * (y::real)) = z";
test "#9*x < #12 * (y::real)";
test "#9*x <= #12 * (y::real)";

test "#-99*x = #132 * (y::real)";
test "(#-99*x) / (#132 * (y::real)) = z";
test "#-99*x < #132 * (y::real)";
test "#-99*x <= #132 * (y::real)";

test "#999*x = #-396 * (y::real)";
test "(#999*x) / (#-396 * (y::real)) = z";
test "#999*x < #-396 * (y::real)";
test "#999*x <= #-396 * (y::real)";

test "#-99*x = #-81 * (y::real)";
test "(#-99*x) / (#-81 * (y::real)) = z";
test "#-99*x <= #-81 * (y::real)";
test "#-99*x < #-81 * (y::real)";

test "#-2 * x = #-1 * (y::real)";
test "#-2 * x = -(y::real)";
test "(#-2 * x) / (#-1 * (y::real)) = z";
test "#-2 * x < -(y::real)";
test "#-2 * x <= #-1 * (y::real)";
test "-x < #-23 * (y::real)";
test "-x <= #-23 * (y::real)";
*)

(*** Simplification of inequalities involving literal divisors ***)

Goal "#0<z ==> ((x::real) <= y/z) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_real_le_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_real_le_divide_eq];

Goal "z<#0 ==> ((x::real) <= y/z) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_real_le_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_real_le_divide_eq];

Goal "#0<z ==> (y/z <= (x::real)) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_real_divide_le_eq";
Addsimps [inst "z" "number_of ?w" pos_real_divide_le_eq];

Goal "z<#0 ==> (y/z <= (x::real)) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_real_divide_le_eq";
Addsimps [inst "z" "number_of ?w" neg_real_divide_le_eq];

Goal "#0<z ==> ((x::real) < y/z) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_real_less_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_real_less_divide_eq];

Goal "z<#0 ==> ((x::real) < y/z) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_real_less_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_real_less_divide_eq];

Goal "#0<z ==> (y/z < (x::real)) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_real_divide_less_eq";
Addsimps [inst "z" "number_of ?w" pos_real_divide_less_eq];

Goal "z<#0 ==> (y/z < (x::real)) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_real_divide_less_eq";
Addsimps [inst "z" "number_of ?w" neg_real_divide_less_eq];

Goal "z~=#0 ==> ((x::real) = y/z) = (x*z = y)";
by (subgoal_tac "(x*z = y) = (x*z = (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "real_eq_divide_eq";
Addsimps [inst "z" "number_of ?w" real_eq_divide_eq];

Goal "z~=#0 ==> (y/z = (x::real)) = (y = x*z)";
by (subgoal_tac "(y = x*z) = ((y/z)*z = x*z)" 1);
by (asm_simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac real_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "real_divide_eq_eq";
Addsimps [inst "z" "number_of ?w" real_divide_eq_eq];


(** Moved from RealOrd.ML to use #0 **)

Goal "[| #0 < r; #0 < x|] ==> (inverse x < inverse (r::real)) = (r < x)";
by (auto_tac (claset() addIs [real_inverse_less_swap], simpset()));
by (res_inst_tac [("t","r")] (real_inverse_inverse RS subst) 1);
by (res_inst_tac [("t","x")] (real_inverse_inverse RS subst) 1);
by (auto_tac (claset() addIs [real_inverse_less_swap],
	      simpset() delsimps [real_inverse_inverse]
			addsimps [real_inverse_gt_zero]));
qed "real_inverse_less_iff";

Goal "[| #0 < r; #0 < x|] ==> (inverse x <= inverse r) = (r <= (x::real))";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                      real_inverse_less_iff]) 1); 
qed "real_inverse_le_iff";

