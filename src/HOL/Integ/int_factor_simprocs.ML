(*  Title:      HOL/int_factor_simprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Factor cancellation simprocs for the integers.

This file can't be combined with int_arith1,2 because it requires IntDiv.thy.
*)

(** Factor cancellation theorems for "int" **)

Goal "!!k::int. (k*m <= k*n) = ((#0 < k --> m<=n) & (k < #0 --> n<=m))";
by (stac zmult_zle_cancel1 1);
by Auto_tac;  
qed "int_mult_le_cancel1";

Goal "!!k::int. (k*m < k*n) = ((#0 < k & m<n) | (k < #0 & n<m))";
by (stac zmult_zless_cancel1 1);
by Auto_tac;  
qed "int_mult_less_cancel1";

Goal "!!k::int. (k*m = k*n) = (k = #0 | m=n)";
by Auto_tac;  
qed "int_mult_eq_cancel1";

Goal "!!k::int. k~=#0 ==> (k*m) div (k*n) = (m div n)";
by (stac zdiv_zmult_zmult1 1); 
by Auto_tac;  
qed "int_mult_div_cancel1";

local
  open Int_Numeral_Simprocs
in

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val trans_tac         = trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s))
                 THEN ALLGOALS
                    (simp_tac (HOL_ss addsimps [zmult_zminus_right RS sym]@
                                               bin_simps@zmult_ac))
  val numeral_simp_tac	= ALLGOALS (simp_tac (HOL_ss addsimps bin_simps))
  val simplify_meta_eq  = simplify_meta_eq mult_1s
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "intdiv_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.intT
  val cancel = int_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "inteq_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.intT
  val cancel = int_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "intless_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.intT
  val cancel = int_mult_less_cancel1 RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = prove_conv "intle_cancel_numeral_factor"
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.intT
  val cancel = int_mult_le_cancel1 RS trans
  val neg_exchanges = true
)

val int_cancel_numeral_factors = 
  map prep_simproc
   [("inteq_cancel_numeral_factors",
     prep_pats ["(l::int) * m = n", "(l::int) = m * n"], 
     EqCancelNumeralFactor.proc),
    ("intless_cancel_numeral_factors", 
     prep_pats ["(l::int) * m < n", "(l::int) < m * n"], 
     LessCancelNumeralFactor.proc),
    ("intle_cancel_numeral_factors", 
     prep_pats ["(l::int) * m <= n", "(l::int) <= m * n"], 
     LeCancelNumeralFactor.proc),
    ("intdiv_cancel_numeral_factors", 
     prep_pats ["((l::int) * m) div n", "(l::int) div (m * n)"], 
     DivCancelNumeralFactor.proc)];

end;

Addsimprocs int_cancel_numeral_factors;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1)); 

test "#9*x = #12 * (y::int)";
test "(#9*x) div (#12 * (y::int)) = z";
test "#9*x < #12 * (y::int)";
test "#9*x <= #12 * (y::int)";

test "#-99*x = #132 * (y::int)";
test "(#-99*x) div (#132 * (y::int)) = z";
test "#-99*x < #132 * (y::int)";
test "#-99*x <= #132 * (y::int)";

test "#999*x = #-396 * (y::int)";
test "(#999*x) div (#-396 * (y::int)) = z";
test "#999*x < #-396 * (y::int)";
test "#999*x <= #-396 * (y::int)";

test "#-99*x = #-81 * (y::int)";
test "(#-99*x) div (#-81 * (y::int)) = z";
test "#-99*x <= #-81 * (y::int)";
test "#-99*x < #-81 * (y::int)";

test "#-2 * x = #-1 * (y::int)";
test "#-2 * x = -(y::int)";
test "(#-2 * x) div (#-1 * (y::int)) = z";
test "#-2 * x < -(y::int)";
test "#-2 * x <= #-1 * (y::int)";
test "-x < #-23 * (y::int)";
test "-x <= #-23 * (y::int)";
*)

