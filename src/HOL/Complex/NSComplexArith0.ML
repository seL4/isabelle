(*  Title:       NSComplexArith0.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Assorted facts that need binary literals 
		 Also, common factor cancellation (see e.g. HyperArith0)
*)

(****
Goal "((x * y = #0) = (x = #0 | y = (#0::hcomplex)))";
by (auto_tac (claset(),simpset() addsimps [rename_numerals hcomplex_mult_zero_iff]));
qed "hcomplex_mult_is_0";
AddIffs [hcomplex_mult_is_0];
****)

(** Division and inverse **)

Goal "0/x = (0::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_divide_def]) 1); 
qed "hcomplex_0_divide";
Addsimps [hcomplex_0_divide];

Goalw [hcomplex_divide_def] "x/(0::hcomplex) = 0";
by (stac HCOMPLEX_INVERSE_ZERO 1); 
by (Simp_tac 1); 
qed "HCOMPLEX_DIVIDE_ZERO";

Goal "inverse (x::hcomplex) = 1/x";
by (simp_tac (simpset() addsimps [hcomplex_divide_def]) 1); 
qed "hcomplex_inverse_eq_divide";

Goal "(inverse(x::hcomplex) = 0) = (x = 0)";
by (Simp_tac 1);
qed "hcomplex_inverse_zero_iff";
Addsimps [hcomplex_inverse_zero_iff];

Goal "(x/y = 0) = (x=0 | y=(0::hcomplex))";
by (auto_tac (claset(), simpset() addsimps [hcomplex_divide_def]));  
qed "hcomplex_divide_eq_0_iff";
Addsimps [hcomplex_divide_eq_0_iff];

Goal "h ~= (0::hcomplex) ==> h/h = 1";
by (asm_simp_tac 
    (simpset() addsimps [hcomplex_divide_def]) 1);
qed "hcomplex_divide_self_eq"; 
Addsimps [hcomplex_divide_self_eq];

bind_thm ("hcomplex_mult_minus_right", hcomplex_minus_mult_eq2 RS sym);

Goal "!!k::hcomplex. (k*m = k*n) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [hcomplex_mult_left_cancel]));  
qed "hcomplex_mult_eq_cancel1";

Goal "!!k::hcomplex. (m*k = n*k) = (k = 0 | m=n)";
by (case_tac "k=0" 1);
by (auto_tac (claset(), simpset() addsimps [hcomplex_mult_right_cancel]));  
qed "hcomplex_mult_eq_cancel2";

Goal "!!k::hcomplex. k~=0 ==> (k*m) / (k*n) = (m/n)";
by (asm_simp_tac
    (simpset() addsimps [hcomplex_divide_def, inverse_mult_distrib]) 1); 
by (subgoal_tac "k * m * (inverse k * inverse n) = \
\                (k * inverse k) * (m * inverse n)" 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps hcomplex_mult_ac) 1); 
qed "hcomplex_mult_div_cancel1";

(*For ExtractCommonTerm*)
Goal "(k*m) / (k*n) = (if k = (0::hcomplex) then 0 else m/n)";
by (simp_tac (simpset() addsimps [hcomplex_mult_div_cancel1]) 1); 
qed "hcomplex_mult_div_cancel_disj";


local
  open HComplex_Numeral_Simprocs
in

val rel_hcomplex_number_of = [eq_hcomplex_number_of];


structure CancelNumeralFactorCommon =
  struct
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps hcomplex_minus_from_mult_simps @ mult_1s))
                 THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps@hcomplex_mult_minus_simps))
                 THEN ALLGOALS (simp_tac (HOL_ss addsimps hcomplex_mult_ac))
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (HOL_ss addsimps rel_hcomplex_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end


structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hcomplexT
  val cancel = hcomplex_mult_div_cancel1 RS trans
  val neg_exchanges = false
)


structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hcomplexT
  val cancel = hcomplex_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)


val hcomplex_cancel_numeral_factors_relations = 
  map prep_simproc
   [("hcomplexeq_cancel_numeral_factor",
    ["(l::hcomplex) * m = n", "(l::hcomplex) = m * n"], 
     EqCancelNumeralFactor.proc)];

val hcomplex_cancel_numeral_factors_divide = prep_simproc
	("hcomplexdiv_cancel_numeral_factor", 
	 ["((l::hcomplex) * m) / n", "(l::hcomplex) / (m * n)", 
                     "((number_of v)::hcomplex) / (number_of w)"], 
	 DivCancelNumeralFactor.proc);

val hcomplex_cancel_numeral_factors = 
    hcomplex_cancel_numeral_factors_relations @ 
    [hcomplex_cancel_numeral_factors_divide];

end;


Addsimprocs hcomplex_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 


test "#9*x = #12 * (y::hcomplex)";
test "(#9*x) / (#12 * (y::hcomplex)) = z";

test "#-99*x = #132 * (y::hcomplex)";

test "#999*x = #-396 * (y::hcomplex)";
test "(#999*x) / (#-396 * (y::hcomplex)) = z";

test "#-99*x = #-81 * (y::hcomplex)";
test "(#-99*x) / (#-81 * (y::hcomplex)) = z";

test "#-2 * x = #-1 * (y::hcomplex)";
test "#-2 * x = -(y::hcomplex)";
test "(#-2 * x) / (#-1 * (y::hcomplex)) = z";

*)


(** Declarations for ExtractCommonTerm **)

local
  open HComplex_Numeral_Simprocs
in

structure CancelFactorCommon =
  struct
  val mk_sum    	= long_mk_prod
  val dest_sum		= dest_prod
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff
  val find_first	= find_first []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@hcomplex_mult_ac))
  end;


structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hcomplexT
  val simplify_meta_eq  = cancel_simplify_meta_eq hcomplex_mult_eq_cancel1
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hcomplexT
  val simplify_meta_eq  = cancel_simplify_meta_eq hcomplex_mult_div_cancel_disj
);

val hcomplex_cancel_factor = 
  map prep_simproc
   [("hcomplex_eq_cancel_factor", ["(l::hcomplex) * m = n", "(l::hcomplex) = m * n"], 
     EqCancelFactor.proc),
    ("hcomplex_divide_cancel_factor", ["((l::hcomplex) * m) / n", "(l::hcomplex) / (m * n)"], 
     DivideCancelFactor.proc)];

end;

Addsimprocs hcomplex_cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1)); 

test "x*k = k*(y::hcomplex)";
test "k = k*(y::hcomplex)"; 
test "a*(b*c) = (b::hcomplex)";
test "a*(b*c) = d*(b::hcomplex)*(x*a)";


test "(x*k) / (k*(y::hcomplex)) = (uu::hcomplex)";
test "(k) / (k*(y::hcomplex)) = (uu::hcomplex)"; 
test "(a*(b*c)) / ((b::hcomplex)) = (uu::hcomplex)";
test "(a*(b*c)) / (d*(b::hcomplex)*(x*a)) = (uu::hcomplex)";

(*FIXME: what do we do about this?*)
test "a*(b*c)/(y*z) = d*(b::hcomplex)*(x*a)/z";
*)


Goal "z~=0 ==> ((x::hcomplex) = y/z) = (x*z = y)";
by (subgoal_tac "(x*z = y) = (x*z = (y/z)*z)" 1);
by (asm_simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hcomplex_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "hcomplex_eq_divide_eq";
Addsimps [inst "z" "number_of ?w" hcomplex_eq_divide_eq];

Goal "z~=0 ==> (y/z = (x::hcomplex)) = (y = x*z)";
by (subgoal_tac "(y = x*z) = ((y/z)*z = x*z)" 1);
by (asm_simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_mult_assoc]) 2); 
by (etac ssubst 1);
by (stac hcomplex_mult_eq_cancel2 1); 
by (Asm_simp_tac 1); 
qed "hcomplex_divide_eq_eq";
Addsimps [inst "z" "number_of ?w" hcomplex_divide_eq_eq];

Goal "(m/k = n/k) = (k = 0 | m = (n::hcomplex))";
by (case_tac "k=0" 1);
by (asm_simp_tac (simpset() addsimps [HCOMPLEX_DIVIDE_ZERO]) 1); 
by (asm_simp_tac (simpset() addsimps [hcomplex_divide_eq_eq, hcomplex_eq_divide_eq, 
                                      hcomplex_mult_eq_cancel2]) 1); 
qed "hcomplex_divide_eq_cancel2";

Goal "(k/m = k/n) = (k = 0 | m = (n::hcomplex))";
by (case_tac "m=0 | n = 0" 1);
by (auto_tac (claset(), 
              simpset() addsimps [HCOMPLEX_DIVIDE_ZERO, hcomplex_divide_eq_eq, 
                                  hcomplex_eq_divide_eq, hcomplex_mult_eq_cancel1]));  
qed "hcomplex_divide_eq_cancel1";

(** Division by 1, -1 **)

Goal "(x::hcomplex)/1 = x";
by (simp_tac (simpset() addsimps [hcomplex_divide_def]) 1); 
qed "hcomplex_divide_1";
Addsimps [hcomplex_divide_1];

Goal "x/-1 = -(x::hcomplex)";
by (Simp_tac 1); 
qed "hcomplex_divide_minus1";
Addsimps [hcomplex_divide_minus1];

Goal "-1/(x::hcomplex) = - (1/x)";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_minus_inverse]) 1); 
qed "hcomplex_minus1_divide";
Addsimps [hcomplex_minus1_divide];


Goal "(x = - y) = (y = - (x::hcomplex))";
by Auto_tac;
qed "hcomplex_equation_minus";

Goal "(- x = y) = (- (y::hcomplex) = x)";
by Auto_tac;
qed "hcomplex_minus_equation";

Goal "(x + - a = (0::hcomplex)) = (x=a)";
by (simp_tac (simpset() addsimps [hcomplex_diff_eq_eq,symmetric hcomplex_diff_def]) 1);
qed "hcomplex_add_minus_iff";
Addsimps [hcomplex_add_minus_iff];

Goal "(-b = -a) = (b = (a::hcomplex))";
by Auto_tac;
qed "hcomplex_minus_eq_cancel";
Addsimps [hcomplex_minus_eq_cancel];

(*Distributive laws for literals*)
Addsimps (map (inst "w" "number_of ?v")
	  [hcomplex_add_mult_distrib, hcomplex_add_mult_distrib2,
	   hcomplex_diff_mult_distrib, hcomplex_diff_mult_distrib2]);

Addsimps [inst "x" "number_of ?v" hcomplex_equation_minus];

Addsimps [inst "y" "number_of ?v" hcomplex_minus_equation];

Goal "(x+y = (0::hcomplex)) = (y = -x)";
by Auto_tac;
by (dtac (sym RS (hcomplex_diff_eq_eq RS iffD2)) 1);
by Auto_tac;  
qed "hcomplex_add_eq_0_iff";
AddIffs [hcomplex_add_eq_0_iff];

Goalw [hcomplex_diff_def]"-(x-y) = y - (x::hcomplex)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_add_commute]));
qed "hcomplex_minus_diff_eq";
Addsimps [hcomplex_minus_diff_eq];

Addsimps [inst "x" "number_of ?w" hcomplex_inverse_eq_divide];

Goal "[|(x::hcomplex) ~= 0;  y ~= 0 |]  \
\     ==> inverse(x) + inverse(y) = (x + y)*inverse(x*y)";
by (asm_full_simp_tac (simpset() addsimps [inverse_mult_distrib,
                    hcomplex_add_mult_distrib,hcomplex_mult_assoc RS sym]) 1);
qed "hcomplex_inverse_add";

Addsimps [hcomplex_of_complex_zero,hcomplex_of_complex_one];
