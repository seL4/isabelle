(*  Title:       hcomplex_arith.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh

Common factor cancellation
*)

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
                 THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (HOL_ss addsimps rel_hcomplex_number_of@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end


structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hcomplexT
  val cancel = mult_divide_cancel_left RS trans
  val neg_exchanges = false
)


structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hcomplexT
  val cancel = field_mult_cancel_left RS trans
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
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@mult_ac))
  end;


structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hcomplexT
  val simplify_meta_eq  = cancel_simplify_meta_eq field_mult_cancel_left
);


structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "HOL.divide"
  val dest_bal = HOLogic.dest_bin "HOL.divide" hcomplexT
  val simplify_meta_eq  = cancel_simplify_meta_eq mult_divide_cancel_eq_if
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


