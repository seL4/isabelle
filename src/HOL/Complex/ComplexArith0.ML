(*  Title:       ComplexArith0.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Assorted facts that need binary literals 
		 Also, common factor cancellation (see e.g. HyperArith0)
*)

local
  open Complex_Numeral_Simprocs
in

val rel_complex_number_of = [eq_complex_number_of];


structure CancelNumeralFactorCommon =
  struct
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =  ALLGOALS (simp_tac (HOL_ss addsimps complex_minus_from_mult_simps @ mult_1s)) 
                  THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@complex_mult_minus_simps))
                  THEN ALLGOALS (simp_tac (HOL_ss addsimps complex_mult_ac))
  val numeral_simp_tac	=  ALLGOALS (simp_tac (HOL_ss addsimps rel_complex_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end


structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" complexT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)


structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" complexT
  val cancel = field_mult_cancel_left RS trans
  val neg_exchanges = false
)

val complex_cancel_numeral_factors_relations = 
  map prep_simproc
   [("complexeq_cancel_numeral_factor",
     ["(l::complex) * m = n", "(l::complex) = m * n"], 
     EqCancelNumeralFactor.proc)];

val complex_cancel_numeral_factors_divide = prep_simproc
	("complexdiv_cancel_numeral_factor", 
	 ["((l::complex) * m) / n", "(l::complex) / (m * n)", 
                     "((number_of v)::complex) / (number_of w)"], 
	 DivCancelNumeralFactor.proc);

val complex_cancel_numeral_factors = 
    complex_cancel_numeral_factors_relations @ 
    [complex_cancel_numeral_factors_divide];

end;


Addsimprocs complex_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 


test "9*x = 12 * (y::complex)";
test "(9*x) / (12 * (y::complex)) = z";

test "-99*x = 132 * (y::complex)";

test "999*x = -396 * (y::complex)";
test "(999*x) / (-396 * (y::complex)) = z";

test "-99*x = -81 * (y::complex)";
test "(-99*x) / (-81 * (y::complex)) = z";

test "-2 * x = -1 * (y::complex)";
test "-2 * x = -(y::complex)";
test "(-2 * x) / (-1 * (y::complex)) = z";

*)


(** Declarations for ExtractCommonTerm **)

local
  open Complex_Numeral_Simprocs
in

structure CancelFactorCommon =
  struct
  val mk_sum    	= long_mk_prod
  val dest_sum		= dest_prod
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff
  val find_first	= find_first []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@complex_mult_ac))
  end;


structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" complexT
  val simplify_meta_eq  = cancel_simplify_meta_eq field_mult_cancel_left
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" complexT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
);

val complex_cancel_factor = 
  map prep_simproc
   [("complex_eq_cancel_factor", ["(l::complex) * m = n", "(l::complex) = m * n"], 
     EqCancelFactor.proc),
    ("complex_divide_cancel_factor", ["((l::complex) * m) / n", "(l::complex) / (m * n)"], 
     DivideCancelFactor.proc)];

end;

Addsimprocs complex_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1)); 

test "x*k = k*(y::complex)";
test "k = k*(y::complex)"; 
test "a*(b*c) = (b::complex)";
test "a*(b*c) = d*(b::complex)*(x*a)";


test "(x*k) / (k*(y::complex)) = (uu::complex)";
test "(k) / (k*(y::complex)) = (uu::complex)"; 
test "(a*(b*c)) / ((b::complex)) = (uu::complex)";
test "(a*(b*c)) / (d*(b::complex)*(x*a)) = (uu::complex)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::complex)*(x*a)/z";
*)


(** Division by 1, -1 **)

Goal "x/-1 = -(x::complex)";
by (Simp_tac 1); 
qed "complex_divide_minus1";
Addsimps [complex_divide_minus1];

Goal "-1/(x::complex) = - (1/x)";
by (simp_tac (simpset() addsimps [complex_divide_def, inverse_minus_eq]) 1); 
qed "complex_minus1_divide";
Addsimps [complex_minus1_divide];

Goal "(x + - a = (0::complex)) = (x=a)";
by (simp_tac (simpset() addsimps [complex_diff_eq_eq,symmetric complex_diff_def]) 1);
qed "complex_add_minus_iff";
Addsimps [complex_add_minus_iff];

Goal "(x+y = (0::complex)) = (y = -x)";
by Auto_tac;
by (dtac (sym RS (complex_diff_eq_eq RS iffD2)) 1);
by Auto_tac;  
qed "complex_add_eq_0_iff";
AddIffs [complex_add_eq_0_iff];


