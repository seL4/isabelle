(*  Title:      HOL/Hyperreal/HyperRealArith0.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Assorted facts that need binary literals and the arithmetic decision procedure

Also, common factor cancellation
*)

Goal "x - - y = x + (y::hypreal)";
by (Simp_tac 1); 
qed "hypreal_diff_minus_eq";
Addsimps [hypreal_diff_minus_eq];

Goal "((x * y = 0) = (x = 0 | y = (0::hypreal)))";
by Auto_tac;  
by (cut_inst_tac [("x","x"),("y","y")] hypreal_mult_zero_disj 1);
by Auto_tac;  
qed "hypreal_mult_is_0";
AddIffs [hypreal_mult_is_0];

(** Division and inverse **)

Goal "0/x = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_0_divide";
Addsimps [hypreal_0_divide];

Goal "((0::hypreal) < inverse x) = (0 < x)";
by (case_tac "x=0" 1);
by (asm_simp_tac (HOL_ss addsimps [HYPREAL_INVERSE_ZERO]) 1); 
by (auto_tac (claset() addDs [hypreal_inverse_less_0], 
              simpset() addsimps [linorder_neq_iff, 
                                  hypreal_inverse_gt_0]));  
qed "hypreal_0_less_inverse_iff";
Addsimps [hypreal_0_less_inverse_iff];

Goal "(inverse x < (0::hypreal)) = (x < 0)";
by (case_tac "x=0" 1);
by (asm_simp_tac (HOL_ss addsimps [HYPREAL_INVERSE_ZERO]) 1); 
by (auto_tac (claset() addDs [hypreal_inverse_less_0], 
              simpset() addsimps [linorder_neq_iff, 
                                  hypreal_inverse_gt_0]));  
qed "hypreal_inverse_less_0_iff";
Addsimps [hypreal_inverse_less_0_iff];

Goal "((0::hypreal) <= inverse x) = (0 <= x)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
qed "hypreal_0_le_inverse_iff";
Addsimps [hypreal_0_le_inverse_iff];

Goal "(inverse x <= (0::hypreal)) = (x <= 0)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
qed "hypreal_inverse_le_0_iff";
Addsimps [hypreal_inverse_le_0_iff];

Goalw [hypreal_divide_def] "x/(0::hypreal) = 0";
by (stac (HYPREAL_INVERSE_ZERO) 1); 
by (Simp_tac 1); 
qed "HYPREAL_DIVIDE_ZERO";

Goal "inverse (x::hypreal) = 1/x";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_inverse_eq_divide";

Goal "((0::hypreal) < x/y) = (0 < x & 0 < y | x < 0 & y < 0)";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_0_less_mult_iff]) 1);
qed "hypreal_0_less_divide_iff";
Addsimps [inst "x" "number_of ?w" hypreal_0_less_divide_iff];

Goal "(x/y < (0::hypreal)) = (0 < x & y < 0 | x < 0 & 0 < y)";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_less_0_iff]) 1);
qed "hypreal_divide_less_0_iff";
Addsimps [inst "x" "number_of ?w" hypreal_divide_less_0_iff];

Goal "((0::hypreal) <= x/y) = ((x <= 0 | 0 <= y) & (0 <= x | y <= 0))";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_0_le_mult_iff]) 1);
by Auto_tac;  
qed "hypreal_0_le_divide_iff";
Addsimps [inst "x" "number_of ?w" hypreal_0_le_divide_iff];

Goal "(x/y <= (0::hypreal)) = ((x <= 0 | y <= 0) & (0 <= x | 0 <= y))";
by (simp_tac (simpset() addsimps [hypreal_divide_def, 
                                  hypreal_mult_le_0_iff]) 1);
by Auto_tac;  
qed "hypreal_divide_le_0_iff";
Addsimps [inst "x" "number_of ?w" hypreal_divide_le_0_iff];

Goal "(inverse(x::hypreal) = 0) = (x = 0)";
by (auto_tac (claset(), 
              simpset() addsimps [HYPREAL_INVERSE_ZERO]));  
by (rtac ccontr 1); 
by (blast_tac (claset() addDs [hypreal_inverse_not_zero]) 1); 
qed "hypreal_inverse_zero_iff";
Addsimps [hypreal_inverse_zero_iff];

Goal "(x/y = 0) = (x=0 | y=(0::hypreal))";
by (auto_tac (claset(), simpset() addsimps [hypreal_divide_def]));  
qed "hypreal_divide_eq_0_iff";
Addsimps [hypreal_divide_eq_0_iff];

Goal "h ~= (0::hypreal) ==> h/h = 1";
by (asm_simp_tac 
    (simpset() addsimps [hypreal_divide_def, hypreal_mult_inverse_left]) 1);
qed "hypreal_divide_self_eq"; 
Addsimps [hypreal_divide_self_eq];


(**** Factor cancellation theorems for "hypreal" ****)

(** Cancellation laws for k*m < k*n and m*k < n*k, also for <= and =,
    but not (yet?) for k*m < n*k. **)

bind_thm ("hypreal_mult_minus_right", hypreal_minus_mult_eq2 RS sym);

Goal "(-y < -x) = ((x::hypreal) < y)";
by (arith_tac 1);
qed "hypreal_minus_less_minus";
Addsimps [hypreal_minus_less_minus];

Goal "[| i<j;  k < (0::hypreal) |] ==> j*k < i*k";
by (rtac (hypreal_minus_less_minus RS iffD1) 1);
by (auto_tac (claset(), 
              simpset() delsimps [hypreal_minus_mult_eq2 RS sym]
                        addsimps [hypreal_minus_mult_eq2,
                                  hypreal_mult_less_mono1])); 
qed "hypreal_mult_less_mono1_neg";

Goal "[| i<j;  k < (0::hypreal) |] ==> k*j < k*i";
by (rtac (hypreal_minus_less_minus RS iffD1) 1);
by (auto_tac (claset(), 
              simpset() delsimps [hypreal_minus_mult_eq1 RS sym]
                        addsimps [hypreal_minus_mult_eq1,
                                  hypreal_mult_less_mono2]));
qed "hypreal_mult_less_mono2_neg";

Goal "[| i <= j;  k <= (0::hypreal) |] ==> j*k <= i*k";
by (auto_tac (claset(), 
          simpset() addsimps [order_le_less, hypreal_mult_less_mono1_neg]));  
qed "hypreal_mult_le_mono1_neg";

Goal "[| i <= j;  k <= (0::hypreal) |] ==> k*j <= k*i";
by (dtac hypreal_mult_le_mono1_neg 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [hypreal_mult_commute])));
qed "hypreal_mult_le_mono2_neg";

Goal "(m*k < n*k) = (((0::hypreal) < k & m<n) | (k < 0 & n<m))";
by (case_tac "k = (0::hypreal)" 1);
by (auto_tac (claset(), 
          simpset() addsimps [linorder_neq_iff, 
                      hypreal_mult_less_mono1, hypreal_mult_less_mono1_neg]));  
by (auto_tac (claset(), 
              simpset() addsimps [linorder_not_less,
				  inst "y1" "m*k" (linorder_not_le RS sym),
                                  inst "y1" "m" (linorder_not_le RS sym)]));
by (TRYALL (etac notE));
by (auto_tac (claset(), 
              simpset() addsimps [order_less_imp_le, hypreal_mult_le_mono1,
                                  hypreal_mult_le_mono1_neg]));  
qed "hypreal_mult_less_cancel2";

Goal "(m*k <= n*k) = (((0::hypreal) < k --> m<=n) & (k < 0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  hypreal_mult_less_cancel2]) 1);
qed "hypreal_mult_le_cancel2";

Goal "(k*m < k*n) = (((0::hypreal) < k & m<n) | (k < 0 & n<m))";
by (simp_tac (simpset() addsimps [inst "z" "k" hypreal_mult_commute, 
                                  hypreal_mult_less_cancel2]) 1);
qed "hypreal_mult_less_cancel1";

Goal "!!k::hypreal. (k*m <= k*n) = ((0 < k --> m<=n) & (k < 0 --> n<=m))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  hypreal_mult_less_cancel1]) 1);
qed "hypreal_mult_le_cancel1";

Goal "!!k::hypreal. (k*m = k*n) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_mult_left_cancel]));  
qed "hypreal_mult_eq_cancel1";

Goal "!!k::hypreal. (m*k = n*k) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_mult_right_cancel]));  
qed "hypreal_mult_eq_cancel2";

Goal "!!k::hypreal. k~=0 ==> (k*m) / (k*n) = (m/n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_divide_def, hypreal_inverse_distrib]) 1); 
by (subgoal_tac "k * m * (inverse k * inverse n) = \
\                (k * inverse k) * (m * inverse n)" 1);
by (asm_full_simp_tac (simpset() addsimps []) 1); 
by (asm_full_simp_tac (HOL_ss addsimps hypreal_mult_ac) 1); 
qed "hypreal_mult_div_cancel1";

(*For ExtractCommonTerm*)
Goal "(k*m) / (k*n) = (if k = (0::hypreal) then 0 else m/n)";
by (simp_tac (simpset() addsimps [hypreal_mult_div_cancel1]) 1); 
qed "hypreal_mult_div_cancel_disj";


local
  open Hyperreal_Numeral_Simprocs
in

val rel_hypreal_number_of = [eq_hypreal_number_of, less_hypreal_number_of, 
                          le_hypreal_number_of_eq_not_less];

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps @ mult_1s))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps hypreal_mult_ac))
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (HOL_ss addsimps rel_hypreal_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hyprealdiv_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hyprealT
  val cancel = hypreal_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hyprealeq_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val cancel = hypreal_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hyprealless_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" hyprealT
  val cancel = hypreal_mult_less_cancel1 RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hyprealle_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" hyprealT
  val cancel = hypreal_mult_le_cancel1 RS trans
  val neg_exchanges = true
)

val hypreal_cancel_numeral_factors_relations = 
  map prep_simproc
   [("hyprealeq_cancel_numeral_factor",
     prep_pats ["(l::hypreal) * m = n", "(l::hypreal) = m * n"], 
     EqCancelNumeralFactor.proc),
    ("hyprealless_cancel_numeral_factor", 
     prep_pats ["(l::hypreal) * m < n", "(l::hypreal) < m * n"], 
     LessCancelNumeralFactor.proc),
    ("hyprealle_cancel_numeral_factor", 
     prep_pats ["(l::hypreal) * m <= n", "(l::hypreal) <= m * n"], 
     LeCancelNumeralFactor.proc)];

val hypreal_cancel_numeral_factors_divide = prep_simproc
	("hyprealdiv_cancel_numeral_factor", 
	 prep_pats ["((l::hypreal) * m) / n", "(l::hypreal) / (m * n)", 
                     "((number_of v)::hypreal) / (number_of w)"], 
	 DivCancelNumeralFactor.proc);

val hypreal_cancel_numeral_factors = 
    hypreal_cancel_numeral_factors_relations @ 
    [hypreal_cancel_numeral_factors_divide];

end;

Addsimprocs hypreal_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 

test "0 <= (y::hypreal) * -2";
test "9*x = 12 * (y::hypreal)";
test "(9*x) / (12 * (y::hypreal)) = z";
test "9*x < 12 * (y::hypreal)";
test "9*x <= 12 * (y::hypreal)";

test "-99*x = 123 * (y::hypreal)";
test "(-99*x) / (123 * (y::hypreal)) = z";
test "-99*x < 123 * (y::hypreal)";
test "-99*x <= 123 * (y::hypreal)";

test "999*x = -396 * (y::hypreal)";
test "(999*x) / (-396 * (y::hypreal)) = z";
test "999*x < -396 * (y::hypreal)";
test "999*x <= -396 * (y::hypreal)";

test "-99*x = -81 * (y::hypreal)";
test "(-99*x) / (-81 * (y::hypreal)) = z";
test "-99*x <= -81 * (y::hypreal)";
test "-99*x < -81 * (y::hypreal)";

test "-2 * x = -1 * (y::hypreal)";
test "-2 * x = -(y::hypreal)";
test "(-2 * x) / (-1 * (y::hypreal)) = z";
test "-2 * x < -(y::hypreal)";
test "-2 * x <= -1 * (y::hypreal)";
test "-x < -23 * (y::hypreal)";
test "-x <= -23 * (y::hypreal)";
*)


(** Declarations for ExtractCommonTerm **)

local
  open Hyperreal_Numeral_Simprocs
in

structure CancelFactorCommon =
  struct
  val mk_sum    	= long_mk_prod
  val dest_sum		= dest_prod
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff
  val find_first	= find_first []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@hypreal_mult_ac))
  end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hypreal_eq_cancel_factor"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val simplify_meta_eq  = cancel_simplify_meta_eq hypreal_mult_eq_cancel1
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Real_Numeral_Simprocs.prove_conv
                     "hypreal_divide_cancel_factor"
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hyprealT
  val simplify_meta_eq  = cancel_simplify_meta_eq hypreal_mult_div_cancel_disj
);

val hypreal_cancel_factor = 
  map prep_simproc
   [("hypreal_eq_cancel_factor",
     prep_pats ["(l::hypreal) * m = n", "(l::hypreal) = m * n"], 
     EqCancelFactor.proc),
    ("hypreal_divide_cancel_factor", 
     prep_pats ["((l::hypreal) * m) / n", "(l::hypreal) / (m * n)"], 
     DivideCancelFactor.proc)];

end;

Addsimprocs hypreal_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1)); 

test "x*k = k*(y::hypreal)";
test "k = k*(y::hypreal)"; 
test "a*(b*c) = (b::hypreal)";
test "a*(b*c) = d*(b::hypreal)*(x*a)";


test "(x*k) / (k*(y::hypreal)) = (uu::hypreal)";
test "(k) / (k*(y::hypreal)) = (uu::hypreal)"; 
test "(a*(b*c)) / ((b::hypreal)) = (uu::hypreal)";
test "(a*(b*c)) / (d*(b::hypreal)*(x*a)) = (uu::hypreal)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::hypreal)*(x*a)/z";
*)


(*** Simplification of inequalities involving literal divisors ***)

Goal "0<z ==> ((x::hypreal) <= y/z) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_hypreal_le_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_hypreal_le_divide_eq];

Goal "z<0 ==> ((x::hypreal) <= y/z) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_hypreal_le_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_hypreal_le_divide_eq];

Goal "0<z ==> (y/z <= (x::hypreal)) = (y <= x*z)";
by (subgoal_tac "(y <= x*z) = ((y/z)*z <= x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_hypreal_divide_le_eq";
Addsimps [inst "z" "number_of ?w" pos_hypreal_divide_le_eq];

Goal "z<0 ==> (y/z <= (x::hypreal)) = (x*z <= y)";
by (subgoal_tac "(x*z <= y) = (x*z <= (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_le_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_hypreal_divide_le_eq";
Addsimps [inst "z" "number_of ?w" neg_hypreal_divide_le_eq];

Goal "0<z ==> ((x::hypreal) < y/z) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_hypreal_less_divide_eq";
Addsimps [inst "z" "number_of ?w" pos_hypreal_less_divide_eq];

Goal "z<0 ==> ((x::hypreal) < y/z) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_hypreal_less_divide_eq";
Addsimps [inst "z" "number_of ?w" neg_hypreal_less_divide_eq];

Goal "0<z ==> (y/z < (x::hypreal)) = (y < x*z)";
by (subgoal_tac "(y < x*z) = ((y/z)*z < x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "pos_hypreal_divide_less_eq";
Addsimps [inst "z" "number_of ?w" pos_hypreal_divide_less_eq];

Goal "z<0 ==> (y/z < (x::hypreal)) = (x*z < y)";
by (subgoal_tac "(x*z < y) = (x*z < (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_less_cancel2 1); 
by (Asm_simp_tac 1); 
qed "neg_hypreal_divide_less_eq";
Addsimps [inst "z" "number_of ?w" neg_hypreal_divide_less_eq];

Goal "z~=0 ==> ((x::hypreal) = y/z) = (x*z = y)";
by (subgoal_tac "(x*z = y) = (x*z = (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "hypreal_eq_divide_eq";
Addsimps [inst "z" "number_of ?w" hypreal_eq_divide_eq];

Goal "z~=0 ==> (y/z = (x::hypreal)) = (y = x*z)";
by (subgoal_tac "(y = x*z) = ((y/z)*z = x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hypreal_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "hypreal_divide_eq_eq";
Addsimps [inst "z" "number_of ?w" hypreal_divide_eq_eq];

Goal "(m/k = n/k) = (k = 0 | m = (n::hypreal))";
by (case_tac "k=0" 1);
by (asm_simp_tac (simpset() addsimps [HYPREAL_DIVIDE_ZERO]) 1); 
by (asm_simp_tac (simpset() addsimps [hypreal_divide_eq_eq, hypreal_eq_divide_eq, 
                                      hypreal_mult_eq_cancel2]) 1); 
qed "hypreal_divide_eq_cancel2";

Goal "(k/m = k/n) = (k = 0 | m = (n::hypreal))";
by (case_tac "m=0 | n = 0" 1);
by (auto_tac (claset(), 
              simpset() addsimps [HYPREAL_DIVIDE_ZERO, hypreal_divide_eq_eq, 
                                  hypreal_eq_divide_eq, hypreal_mult_eq_cancel1]));  
qed "hypreal_divide_eq_cancel1";

Goal "[| 0 < r; 0 < x|] ==> (inverse x < inverse (r::hypreal)) = (r < x)";
by (auto_tac (claset() addIs [hypreal_inverse_less_swap], simpset()));
by (res_inst_tac [("t","r")] (hypreal_inverse_inverse RS subst) 1);
by (res_inst_tac [("t","x")] (hypreal_inverse_inverse RS subst) 1);
by (auto_tac (claset() addIs [hypreal_inverse_less_swap],
	      simpset() delsimps [hypreal_inverse_inverse]
			addsimps [hypreal_inverse_gt_0]));
qed "hypreal_inverse_less_iff";

Goal "[| 0 < r; 0 < x|] ==> (inverse x <= inverse r) = (r <= (x::hypreal))";
by (asm_simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                      hypreal_inverse_less_iff]) 1); 
qed "hypreal_inverse_le_iff";

(** Division by 1, -1 **)

Goal "(x::hypreal)/1 = x";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_divide_1";
Addsimps [hypreal_divide_1];

Goal "x/-1 = -(x::hypreal)";
by (Simp_tac 1); 
qed "hypreal_divide_minus1";
Addsimps [hypreal_divide_minus1];

Goal "-1/(x::hypreal) = - (1/x)";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_minus_inverse]) 1); 
qed "hypreal_minus1_divide";
Addsimps [hypreal_minus1_divide];

Goal "[| (0::hypreal) < d1; 0 < d2 |] ==> EX e. 0 < e & e < d1 & e < d2";
by (res_inst_tac [("x","(min d1 d2)/2")] exI 1); 
by (asm_simp_tac (simpset() addsimps [min_def]) 1); 
qed "hypreal_lbound_gt_zero";


(*** General rewrites to improve automation, like those for type "int" ***)

(** The next several equations can make the simplifier loop! **)

Goal "(x < - y) = (y < - (x::hypreal))";
by Auto_tac;  
qed "hypreal_less_minus"; 

Goal "(- x < y) = (- y < (x::hypreal))";
by Auto_tac;  
qed "hypreal_minus_less"; 

Goal "(x <= - y) = (y <= - (x::hypreal))";
by Auto_tac;  
qed "hypreal_le_minus"; 

Goal "(- x <= y) = (- y <= (x::hypreal))";
by Auto_tac;  
qed "hypreal_minus_le"; 

Goal "(x = - y) = (y = - (x::hypreal))";
by Auto_tac;
qed "hypreal_equation_minus";

Goal "(- x = y) = (- (y::hypreal) = x)";
by Auto_tac;
qed "hypreal_minus_equation";

Goal "(x + - a = (0::hypreal)) = (x=a)";
by (arith_tac 1);
qed "hypreal_add_minus_iff";
Addsimps [hypreal_add_minus_iff];

Goal "(-b = -a) = (b = (a::hypreal))";
by (arith_tac 1);
qed "hypreal_minus_eq_cancel";
Addsimps [hypreal_minus_eq_cancel];

Goal "(-s <= -r) = ((r::hypreal) <= s)";
by (stac hypreal_minus_le 1); 
by (Simp_tac 1); 
qed "hypreal_le_minus_iff";
Addsimps [hypreal_le_minus_iff];          


(*Distributive laws for literals*)
Addsimps (map (inst "w" "number_of ?v")
	  [hypreal_add_mult_distrib, hypreal_add_mult_distrib2,
	   hypreal_diff_mult_distrib, hypreal_diff_mult_distrib2]);

Addsimps (map (inst "x" "number_of ?v") 
	  [hypreal_less_minus, hypreal_le_minus, hypreal_equation_minus]);
Addsimps (map (inst "y" "number_of ?v") 
	  [hypreal_minus_less, hypreal_minus_le, hypreal_minus_equation]);

Addsimps (map (simplify (simpset()) o inst "x" "1") 
	  [hypreal_less_minus, hypreal_le_minus, hypreal_equation_minus]);
Addsimps (map (simplify (simpset()) o inst "y" "1") 
	  [hypreal_minus_less, hypreal_minus_le, hypreal_minus_equation]);

(*** Simprules combining x+y and 0 ***)

Goal "(x+y = (0::hypreal)) = (y = -x)";
by Auto_tac;  
qed "hypreal_add_eq_0_iff";
AddIffs [hypreal_add_eq_0_iff];

Goal "(x+y < (0::hypreal)) = (y < -x)";
by Auto_tac;  
qed "hypreal_add_less_0_iff";
AddIffs [hypreal_add_less_0_iff];

Goal "((0::hypreal) < x+y) = (-x < y)";
by Auto_tac;  
qed "hypreal_0_less_add_iff";
AddIffs [hypreal_0_less_add_iff];

Goal "(x+y <= (0::hypreal)) = (y <= -x)";
by Auto_tac;  
qed "hypreal_add_le_0_iff";
AddIffs [hypreal_add_le_0_iff];

Goal "((0::hypreal) <= x+y) = (-x <= y)";
by Auto_tac;  
qed "hypreal_0_le_add_iff";
AddIffs [hypreal_0_le_add_iff];


(** Simprules combining x-y and 0; see also hypreal_less_iff_diff_less_0 etc
    in HyperBin
**)

Goal "((0::hypreal) < x-y) = (y < x)";
by Auto_tac;  
qed "hypreal_0_less_diff_iff";
AddIffs [hypreal_0_less_diff_iff];

Goal "((0::hypreal) <= x-y) = (y <= x)";
by Auto_tac;  
qed "hypreal_0_le_diff_iff";
AddIffs [hypreal_0_le_diff_iff];

(*
FIXME: we should have this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric hypreal_diff_def];
*)

Goal "-(x-y) = y - (x::hypreal)";
by (arith_tac 1);
qed "hypreal_minus_diff_eq";
Addsimps [hypreal_minus_diff_eq];


(*** Density of the Hyperreals ***)

Goal "x < y ==> x < (x+y) / (2::hypreal)";
by Auto_tac;
qed "hypreal_less_half_sum";

Goal "x < y ==> (x+y)/(2::hypreal) < y";
by Auto_tac;
qed "hypreal_gt_half_sum";

Goal "x < y ==> EX r::hypreal. x < r & r < y";
by (blast_tac (claset() addSIs [hypreal_less_half_sum, hypreal_gt_half_sum]) 1);
qed "hypreal_dense";


(*Replaces "inverse #nn" by 1/#nn *)
Addsimps [inst "x" "number_of ?w" hypreal_inverse_eq_divide];


