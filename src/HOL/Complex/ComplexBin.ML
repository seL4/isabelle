(*  Title:      ComplexBin.ML
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
    Descrition: Binary arithmetic for the complex numbers
*)

(** complex_of_real (coercion from real to complex) **)

Goal "complex_of_real (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [complex_number_of_def]) 1);
qed "complex_number_of";
Addsimps [complex_number_of];
 
Goalw [complex_number_of_def] "Numeral0 = (0::complex)";
by (Simp_tac 1);
qed "complex_numeral_0_eq_0";
 
Goalw [complex_number_of_def] "Numeral1 = (1::complex)";
by (Simp_tac 1);
qed "complex_numeral_1_eq_1";

(** Addition **)

Goal "(number_of v :: complex) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (HOL_ss addsimps [complex_number_of_def, 
                      complex_of_real_add, add_real_number_of]) 1);
qed "add_complex_number_of";
Addsimps [add_complex_number_of];


(** Subtraction **)

Goalw [complex_number_of_def]
     "- (number_of w :: complex) = number_of (bin_minus w)";
by (simp_tac
    (HOL_ss addsimps [minus_real_number_of, complex_of_real_minus RS sym]) 1);
qed "minus_complex_number_of";
Addsimps [minus_complex_number_of];

Goalw [complex_number_of_def, complex_diff_def]
     "(number_of v :: complex) - number_of w = number_of (bin_add v (bin_minus w))";
by (Simp_tac 1); 
qed "diff_complex_number_of";
Addsimps [diff_complex_number_of];


(** Multiplication **)

Goal "(number_of v :: complex) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (HOL_ss addsimps [complex_number_of_def, 
	              complex_of_real_mult, mult_real_number_of]) 1);
qed "mult_complex_number_of";
Addsimps [mult_complex_number_of];

Goal "(2::complex) = 1 + 1";
by (simp_tac (simpset() addsimps [complex_numeral_1_eq_1 RS sym]) 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "2 * z = (z+z::complex)";
by (simp_tac (simpset () addsimps [lemma, left_distrib]) 1);
qed "complex_mult_2";

Goal "z * 2 = (z+z::complex)";
by (stac mult_commute 1 THEN rtac complex_mult_2 1);
qed "complex_mult_2_right";

(** Equals (=) **)

Goal "((number_of v :: complex) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')) :: int)";
by (simp_tac
    (HOL_ss addsimps [complex_number_of_def, 
	              complex_of_real_eq_iff, eq_real_number_of]) 1);
qed "eq_complex_number_of";
Addsimps [eq_complex_number_of];

(*** New versions of existing theorems involving 0, 1 ***)

Goal "- 1 = (-1::complex)";
by (simp_tac (simpset() addsimps [complex_numeral_1_eq_1 RS sym]) 1);
qed "complex_minus_1_eq_m1";

Goal "-1 * z = -(z::complex)";
by (simp_tac (simpset() addsimps [complex_minus_1_eq_m1 RS sym]) 1);
qed "complex_mult_minus1";

Goal "z * -1 = -(z::complex)";
by (stac mult_commute 1 THEN rtac complex_mult_minus1 1);
qed "complex_mult_minus1_right";

Addsimps [complex_mult_minus1,complex_mult_minus1_right];


(*Maps 0 to Numeral0 and 1 to Numeral1 and -Numeral1 to -1*)
val complex_numeral_ss = 
    hypreal_numeral_ss addsimps [complex_numeral_0_eq_0 RS sym, complex_numeral_1_eq_1 RS sym, 
		                 complex_minus_1_eq_m1];

fun rename_numerals th = 
    asm_full_simplify complex_numeral_ss (Thm.transfer (the_context ()) th);

(*Now insert some identities previously stated for 0 and 1c*)

Addsimps [complex_numeral_0_eq_0,complex_numeral_1_eq_1];

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::complex)";
by (auto_tac (claset(),simpset() addsimps [complex_add_assoc RS sym]));
qed "complex_add_number_of_left";

Goal "number_of v *(number_of w * z) = (number_of(bin_mult v w) * z::complex)";
by (simp_tac (simpset() addsimps [mult_assoc RS sym]) 1);
qed "complex_mult_number_of_left";

Goalw [complex_diff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::complex)";
by (rtac complex_add_number_of_left 1);
qed "complex_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\     number_of (bin_add v (bin_minus w)) + (c::complex)";
by (auto_tac (claset(),simpset() addsimps [complex_diff_def]@ add_ac));
qed "complex_add_number_of_diff2";

Addsimps [complex_add_number_of_left, complex_mult_number_of_left,
	  complex_add_number_of_diff1, complex_add_number_of_diff2]; 


(**** Simprocs for numeric literals ****)

(** Combining of literal coefficients in sums of products **)

Goal "(x = y) = (x-y = (0::complex))";
by (simp_tac (simpset() addsimps [diff_eq_eq]) 1);   
qed "complex_eq_iff_diff_eq_0";



structure Complex_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [complex_numeral_0_eq_0 RS sym, complex_numeral_1_eq_1 RS sym];


(*Utilities*)

val complexT = Type("Complex.complex",[]);

fun mk_numeral n = HOLogic.number_of_const complexT $ HOLogic.mk_bin n;

val dest_numeral = Real_Numeral_Simprocs.dest_numeral;
val find_first_numeral = Real_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", complexT --> complexT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" complexT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
	if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" complexT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" complexT;

fun dest_prod t =
      let val (t,u) = dest_times t 
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*) 
fun mk_coeff (k, ts) = mk_times (mk_numeral k, ts);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const ("uminus", _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term.term_ord (dest_prod t)
	val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", []) 
  | find_first_coeff past u (t::terms) =
	let val (n,u') = dest_coeff 1 t
	in  if u aconv u' then (n, rev past @ terms)
			  else find_first_coeff (t::past) u terms
	end
	handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify Numeral0+n, n+Numeral0, Numeral1*n, n*Numeral1*)
val add_0s = map rename_numerals [complex_add_zero_left, complex_add_zero_right];
val mult_plus_1s = map rename_numerals [complex_mult_one_left, complex_mult_one_right];
val mult_minus_1s = map rename_numerals
                      [complex_mult_minus1, complex_mult_minus1_right];
val mult_1s = mult_plus_1s @ mult_minus_1s;

(*To perform binary arithmetic*)
val bin_simps =
    [complex_numeral_0_eq_0 RS sym, complex_numeral_1_eq_1 RS sym,
     add_complex_number_of, complex_add_number_of_left, 
     minus_complex_number_of, diff_complex_number_of, mult_complex_number_of, 
     complex_mult_number_of_left] @ bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [complex_add_number_of_left, add_complex_number_of];

(*To evaluate binary negations of coefficients*)
val complex_minus_simps = NCons_simps @
                   [complex_minus_1_eq_m1,minus_complex_number_of, 
		    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
		    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [complex_diff_def, minus_add_distrib, minus_minus];

(* push the unary minus down: - x * y = x * - y *)
val complex_minus_mult_eq_1_to_2 = 
    [minus_mult_left RS sym, minus_mult_right] MRS trans 
    |> standard;

(*to extract again any uncancelled minuses*)
val complex_minus_from_mult_simps = 
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val complex_mult_minus_simps =
    [mult_assoc, minus_mult_left, complex_minus_mult_eq_1_to_2];

(*Final simplification: cancel + and *  *)
val simplify_meta_eq = 
    Int_Numeral_Simprocs.simplify_meta_eq
         [add_zero_left, add_zero_right,
 	  mult_zero_left, mult_zero_right, mult_1, mult_1_right];

val prep_simproc = Real_Numeral_Simprocs.prep_simproc;


structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val find_first_coeff	= find_first_coeff []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         complex_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@complex_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps complex_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" complexT
  val bal_add1 = eq_add_iff1 RS trans
  val bal_add2 = eq_add_iff2 RS trans
);


val cancel_numerals = 
  map prep_simproc
   [("complexeq_cancel_numerals",
               ["(l::complex) + m = n", "(l::complex) = m + n", 
		"(l::complex) - m = n", "(l::complex) = m - n", 
		"(l::complex) * m = n", "(l::complex) = m * n"], 
     EqCancelNumerals.proc)];

structure CombineNumeralsData =
  struct
  val add		= op + : int*int -> int 
  val mk_sum    	= long_mk_sum    (*to work for e.g. #2*x + #3*x *)
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val left_distrib	= combine_common_factor RS trans
  val prove_conv	= Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac = 
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         complex_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@complex_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps complex_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac	= ALLGOALS 
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals = 
    prep_simproc ("complex_combine_numerals",
		  ["(i::complex) + j", "(i::complex) - j"],
		  CombineNumerals.proc);


(** Declarations for ExtractCommonTerm **)

(*this version ALWAYS includes a trailing one*)
fun long_mk_prod []        = one
  | long_mk_prod (t :: ts) = mk_times (t, mk_prod ts);

(*Find first term that matches u*)
fun find_first past u []         = raise TERM("find_first", []) 
  | find_first past u (t::terms) =
	if u aconv t then (rev past @ terms)
        else find_first (t::past) u terms
	handle TERM _ => find_first (t::past) u terms;

(*Final simplification: cancel + and *  *)
fun cancel_simplify_meta_eq cancel_th th = 
    Int_Numeral_Simprocs.simplify_meta_eq 
        [complex_mult_one_left, complex_mult_one_right] 
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure ComplexAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = complex_numeral_0_eq_0
  val numeral_1_eq_1  = complex_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end;

structure ComplexAbstractNumerals = AbstractNumeralsFun (ComplexAbstractNumeralsData);

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("complex_add_eval_numerals",
     ["(m::complex) + 1", "(m::complex) + number_of v"],
     ComplexAbstractNumerals.proc add_complex_number_of),
    ("complex_diff_eval_numerals",
     ["(m::complex) - 1", "(m::complex) - number_of v"],
     ComplexAbstractNumerals.proc diff_complex_number_of),
    ("complex_eq_eval_numerals",
     ["(m::complex) = 0", "(m::complex) = 1", "(m::complex) = number_of v"],
     ComplexAbstractNumerals.proc eq_complex_number_of)];

end;

Addsimprocs Complex_Numeral_Simprocs.eval_numerals;
Addsimprocs Complex_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Complex_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "l +  2 +  2 +  2 + (l +  2) + (oo +  2) = (uu::complex)";
test " 2*u = (u::complex)";
test "(i + j +  12 + (k::complex)) -  15 = y";
test "(i + j +  12 + (k::complex)) -  5 = y";

test "( 2*x - (u*v) + y) - v* 3*u = (w::complex)";
test "( 2*x*u*v + (u*v)* 4 + y) - v*u* 4 = (w::complex)";
test "( 2*x*u*v + (u*v)* 4 + y) - v*u = (w::complex)";
test "u*v - (x*u*v + (u*v)* 4 + y) = (w::complex)";

test "(i + j +  12 + (k::complex)) = u +  15 + y";
test "(i + j* 2 +  12 + (k::complex)) = j +  5 + y";

test " 2*y +  3*z +  6*w +  2*y +  3*z +  2*u =  2*y' +  3*z' +  6*w' +  2*y' +  3*z' + u + (vv::complex)";

test "a + -(b+c) + b = (d::complex)";
test "a + -(b+c) - b = (d::complex)";

(*negative numerals*)
test "(i + j +  -2 + (k::complex)) - (u +  5 + y) = zz";

test "(i + j +  -12 + (k::complex)) -  15 = y";
test "(i + j +  12 + (k::complex)) -  -15 = y";
test "(i + j +  -12 + (k::complex)) -  -15 = y";

*)


(** Constant folding for complex plus and times **)

structure Complex_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T	     = Complex_Numeral_Simprocs.complexT
  val plus   = Const ("op *", [T,T] ---> T)
  val add_ac = mult_ac
end;

structure Complex_Times_Assoc = Assoc_Fold (Complex_Times_Assoc_Data);

Addsimprocs [Complex_Times_Assoc.conv];

Addsimps [complex_of_real_zero_iff];


(*Convert???
Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + ii * number_of ya = \
\       number_of xb) = \
\  (((number_of xa :: complex) = number_of xb) & \
\   ((number_of ya :: complex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff2,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff2";
Addsimps [complex_number_of_eq_cancel_iff2];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + number_of ya * ii = \
\       number_of xb) = \
\  (((number_of xa :: complex) = number_of xb) & \
\   ((number_of ya :: complex) = 0))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff2a,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff2a";
Addsimps [complex_number_of_eq_cancel_iff2a];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + ii * number_of ya = \
\    ii * number_of yb) = \
\  (((number_of xa :: complex) = 0) & \
\   ((number_of ya :: complex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff3,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff3";
Addsimps [complex_number_of_eq_cancel_iff3];

Goalw [complex_number_of_def] 
  "((number_of xa :: complex) + number_of ya * ii= \
\    ii * number_of yb) = \
\  (((number_of xa :: complex) = 0) & \
\   ((number_of ya :: complex) = number_of yb))";
by (auto_tac (claset(), HOL_ss addsimps [complex_eq_cancel_iff3a,
    complex_of_real_zero_iff]));
qed "complex_number_of_eq_cancel_iff3a";
Addsimps [complex_number_of_eq_cancel_iff3a];
*)

Goalw [complex_number_of_def] "cnj (number_of v :: complex) = number_of v";
by (rtac complex_cnj_complex_of_real 1);
qed "complex_number_of_cnj";
Addsimps [complex_number_of_cnj];

Goalw [complex_number_of_def] 
      "cmod(number_of v :: complex) = abs (number_of v :: real)";
by (auto_tac (claset(), HOL_ss addsimps [complex_mod_complex_of_real]));
qed "complex_number_of_cmod";
Addsimps [complex_number_of_cmod];

Goalw [complex_number_of_def] 
      "Re(number_of v :: complex) = number_of v";
by (auto_tac (claset(), HOL_ss addsimps [Re_complex_of_real]));
qed "complex_number_of_Re";
Addsimps [complex_number_of_Re];

Goalw [complex_number_of_def] 
      "Im(number_of v :: complex) = 0";
by (auto_tac (claset(), HOL_ss addsimps [Im_complex_of_real]));
qed "complex_number_of_Im";
Addsimps [complex_number_of_Im];

Goalw [expi_def] 
   "expi((2::complex) * complex_of_real pi * ii) = 1";
by (auto_tac (claset(),simpset() addsimps [complex_Re_mult_eq,
    complex_Im_mult_eq,cis_def]));
qed "expi_two_pi_i";
Addsimps [expi_two_pi_i];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1)); 

test "23 * ii + 45 * ii= (x::complex)";

test "5 * ii + 12 - 45 * ii= (x::complex)";
test "5 * ii + 40 - 12 * ii + 9 = (x::complex) + 89 * ii";
test "5 * ii + 40 - 12 * ii + 9 - 78 = (x::complex) + 89 * ii";

test "l + 10 * ii + 90 + 3*l +  9 + 45 * ii= (x::complex)";
test "87 + 10 * ii + 90 + 3*7 +  9 + 45 * ii= (x::complex)";


*)
