(*  Title:       ComplexArith0.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Assorted facts that need binary literals 
		 Also, common factor cancellation (see e.g. HyperArith0)
*)

(** Division and inverse **)

Goal "0/x = (0::complex)";
by (simp_tac (simpset() addsimps [complex_divide_def]) 1); 
qed "complex_0_divide";
Addsimps [complex_0_divide];

Goalw [complex_divide_def] "x/(0::complex) = 0";
by (stac COMPLEX_INVERSE_ZERO 1); 
by (Simp_tac 1); 
qed "COMPLEX_DIVIDE_ZERO";

Goal "inverse (x::complex) = 1/x";
by (simp_tac (simpset() addsimps [complex_divide_def]) 1); 
qed "complex_inverse_eq_divide";

Goal "(inverse(x::complex) = 0) = (x = 0)";
by (auto_tac (claset(), 
              simpset() addsimps [COMPLEX_INVERSE_ZERO]));  
qed "complex_inverse_zero_iff";
Addsimps [complex_inverse_zero_iff];

Goal "(x/y = 0) = (x=0 | y=(0::complex))";
by (auto_tac (claset(), simpset() addsimps [complex_divide_def]));  
qed "complex_divide_eq_0_iff";
Addsimps [complex_divide_eq_0_iff];

Goal "h ~= (0::complex) ==> h/h = 1";
by (asm_simp_tac 
    (simpset() addsimps [complex_divide_def]) 1);
qed "complex_divide_self_eq"; 
Addsimps [complex_divide_self_eq];

bind_thm ("complex_mult_minus_right", complex_minus_mult_eq2 RS sym);

Goal "!!k::complex. (k*m = k*n) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [complex_mult_left_cancel]));  
qed "complex_mult_eq_cancel1";

Goal "!!k::complex. (m*k = n*k) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [complex_mult_right_cancel]));  
qed "complex_mult_eq_cancel2";

Goal "!!k::complex. k~=0 ==> (k*m) / (k*n) = (m/n)";
by (asm_simp_tac
    (simpset() addsimps [complex_divide_def, complex_inverse_distrib]) 1); 
by (subgoal_tac "k * m * (inverse k * inverse n) = \
\                (k * inverse k) * (m * inverse n)" 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps complex_mult_ac) 1); 
qed "complex_mult_div_cancel1";

(*For ExtractCommonTerm*)
Goal "(k*m) / (k*n) = (if k = (0::complex) then 0 else m/n)";
by (simp_tac (simpset() addsimps [complex_mult_div_cancel1]) 1); 
qed "complex_mult_div_cancel_disj";


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
  val cancel = complex_mult_div_cancel1 RS trans
  val neg_exchanges = false
)


structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" complexT
  val cancel = complex_mult_eq_cancel1 RS trans
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
  val simplify_meta_eq  = cancel_simplify_meta_eq complex_mult_eq_cancel1
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" complexT
  val simplify_meta_eq  = cancel_simplify_meta_eq complex_mult_div_cancel_disj
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


Goal "z~=0 ==> ((x::complex) = y/z) = (x*z = y)";
by (subgoal_tac "(x*z = y) = (x*z = (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [complex_divide_def, complex_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac complex_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "complex_eq_divide_eq";
Addsimps [inst "z" "number_of ?w" complex_eq_divide_eq];

Goal "z~=0 ==> (y/z = (x::complex)) = (y = x*z)";
by (subgoal_tac "(y = x*z) = ((y/z)*z = x*z)" 1);
by (asm_simp_tac (simpset() addsimps [complex_divide_def, complex_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac complex_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "complex_divide_eq_eq";
Addsimps [inst "z" "number_of ?w" complex_divide_eq_eq];

Goal "(m/k = n/k) = (k = 0 | m = (n::complex))";
by (case_tac "k=0" 1);
by (asm_simp_tac (simpset() addsimps [COMPLEX_DIVIDE_ZERO]) 1); 
by (asm_simp_tac (simpset() addsimps [complex_divide_eq_eq, complex_eq_divide_eq, 
                                      complex_mult_eq_cancel2]) 1); 
qed "complex_divide_eq_cancel2";

Goal "(k/m = k/n) = (k = 0 | m = (n::complex))";
by (case_tac "m=0 | n = 0" 1);
by (auto_tac (claset(), 
              simpset() addsimps [COMPLEX_DIVIDE_ZERO, complex_divide_eq_eq, 
                                  complex_eq_divide_eq, complex_mult_eq_cancel1]));  
qed "complex_divide_eq_cancel1";

(** Division by 1, -1 **)

Goal "(x::complex)/1 = x";
by (simp_tac (simpset() addsimps [complex_divide_def]) 1); 
qed "complex_divide_1";
Addsimps [complex_divide_1];

Goal "x/-1 = -(x::complex)";
by (Simp_tac 1); 
qed "complex_divide_minus1";
Addsimps [complex_divide_minus1];

Goal "-1/(x::complex) = - (1/x)";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_minus_inverse]) 1); 
qed "complex_minus1_divide";
Addsimps [complex_minus1_divide];


Goal "(x = - y) = (y = - (x::complex))";
by Auto_tac;
qed "complex_equation_minus";

Goal "(- x = y) = (- (y::complex) = x)";
by Auto_tac;
qed "complex_minus_equation";

Goal "(x + - a = (0::complex)) = (x=a)";
by (simp_tac (simpset() addsimps [complex_diff_eq_eq,symmetric complex_diff_def]) 1);
qed "complex_add_minus_iff";
Addsimps [complex_add_minus_iff];

Goal "(-b = -a) = (b = (a::complex))";
by Auto_tac;
qed "complex_minus_eq_cancel";
Addsimps [complex_minus_eq_cancel];

(*Distributive laws for literals*)
Addsimps (map (inst "w" "number_of ?v")
	  [complex_add_mult_distrib, complex_add_mult_distrib2,
	   complex_diff_mult_distrib, complex_diff_mult_distrib2]);

Addsimps [inst "x" "number_of ?v" complex_equation_minus];

Addsimps [inst "y" "number_of ?v" complex_minus_equation];

Goal "(x+y = (0::complex)) = (y = -x)";
by Auto_tac;
by (dtac (sym RS (complex_diff_eq_eq RS iffD2)) 1);
by Auto_tac;  
qed "complex_add_eq_0_iff";
AddIffs [complex_add_eq_0_iff];

Goalw [complex_diff_def]"-(x-y) = y - (x::complex)";
by (auto_tac (claset(),simpset() addsimps [complex_add_commute]));
qed "complex_minus_diff_eq";
Addsimps [complex_minus_diff_eq];

Addsimps [inst "x" "number_of ?w" complex_inverse_eq_divide];

