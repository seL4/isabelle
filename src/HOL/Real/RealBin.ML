(*  Title:      HOL/Real/RealBin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the reals (integer literals only).
*)

(** real (coercion from int to real) **)

Goal "real (number_of w :: int) = number_of w";
by (simp_tac (simpset() addsimps [real_number_of_def]) 1);
qed "real_number_of";
Addsimps [real_number_of];

Goalw [real_number_of_def] "Numeral0 = (0::real)";
by (simp_tac (simpset() addsimps [real_of_int_zero RS sym]) 1);
qed "real_numeral_0_eq_0";

Goalw [real_number_of_def] "Numeral1 = (1::real)";
by (stac (real_of_one RS sym) 1);
by (Simp_tac 1);
qed "real_numeral_1_eq_1";

(** Addition **)

Goal "(number_of v :: real) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (HOL_ss addsimps [real_number_of_def,
                                  real_of_int_add, number_of_add]) 1);
qed "add_real_number_of";

Addsimps [add_real_number_of];


(** Subtraction **)

Goalw [real_number_of_def] "- (number_of w :: real) = number_of (bin_minus w)";
by (simp_tac
    (HOL_ss addsimps [number_of_minus, real_of_int_minus]) 1);
qed "minus_real_number_of";

Goalw [real_number_of_def]
   "(number_of v :: real) - number_of w = number_of (bin_add v (bin_minus w))";
by (simp_tac
    (HOL_ss addsimps [diff_number_of_eq, real_of_int_diff]) 1);
qed "diff_real_number_of";

Addsimps [minus_real_number_of, diff_real_number_of];


(** Multiplication **)

Goal "(number_of v :: real) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (HOL_ss addsimps [real_number_of_def, real_of_int_mult,
                      number_of_mult]) 1);
qed "mult_real_number_of";

Addsimps [mult_real_number_of];

Goal "(2::real) = 1 + 1";
by (simp_tac (simpset() addsimps [real_numeral_1_eq_1 RS sym]) 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "2 * z = (z+z::real)";
by (simp_tac (simpset () addsimps [lemma, left_distrib]) 1);
qed "real_mult_2";

Goal "z * 2 = (z+z::real)";
by (stac real_mult_commute 1 THEN rtac real_mult_2 1);
qed "real_mult_2_right";


(*** Comparisons ***)

(** Equals (=) **)

Goal "((number_of v :: real) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [real_number_of_def,
                      real_of_int_inject, eq_number_of_eq]) 1);
qed "eq_real_number_of";

Addsimps [eq_real_number_of];

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: real) < number_of v') = \
\     neg (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [real_number_of_def, real_of_int_less_iff,
                                  less_number_of_eq_neg]) 1);
qed "less_real_number_of";

Addsimps [less_real_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::real)) = \
\     (~ number_of y < (number_of x::real))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_real_number_of_eq_not_less";

Addsimps [le_real_number_of_eq_not_less];

(*** New versions of existing theorems involving 0, 1 ***)

Goal "- 1 = (-1::real)";
by (simp_tac (simpset() addsimps [real_numeral_1_eq_1 RS sym]) 1);
qed "real_minus_1_eq_m1";

Goal "-1 * z = -(z::real)";
by (simp_tac (simpset() addsimps [real_minus_1_eq_m1 RS sym]) 1);
qed "real_mult_minus1";

Goal "z * -1 = -(z::real)";
by (stac real_mult_commute 1 THEN rtac real_mult_minus1 1);
qed "real_mult_minus1_right";

Addsimps [real_mult_minus1, real_mult_minus1_right];


(*Maps 0 to Numeral0 and 1 to Numeral1 and -(Numeral1) to -1*)
val real_numeral_ss =
    HOL_ss addsimps [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym,
                     real_minus_1_eq_m1];

fun rename_numerals th =
    asm_full_simplify real_numeral_ss (Thm.transfer (the_context ()) th);


(** real from type "nat" **)

Goal "(0 < real (n::nat)) = (0<n)";
by (simp_tac (HOL_ss addsimps [real_of_nat_less_iff,
                               real_of_nat_zero RS sym]) 1);
qed "zero_less_real_of_nat_iff";
AddIffs [zero_less_real_of_nat_iff];

Goal "(0 <= real (n::nat)) = (0<=n)";
by (simp_tac (HOL_ss addsimps [real_of_nat_le_iff,
                               real_of_nat_zero RS sym]) 1);
qed "zero_le_real_of_nat_iff";
AddIffs [zero_le_real_of_nat_iff];


(*Like the ones above, for "equals"*)
AddIffs [real_of_nat_zero_iff];

(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::real)";
by (asm_full_simp_tac (simpset() addsimps [add_assoc RS sym]) 1); 
qed "real_add_number_of_left";

Goal "number_of v * (number_of w * z) = (number_of(bin_mult v w) * z::real)";
by (simp_tac (simpset() addsimps [mult_assoc RS sym]) 1);
qed "real_mult_number_of_left";

Goalw [real_diff_def]
     "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::real)";
by (rtac real_add_number_of_left 1);
qed "real_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\     number_of (bin_add v (bin_minus w)) + (c::real)";
by (stac (diff_real_number_of RS sym) 1);
by (asm_full_simp_tac (HOL_ss addsimps [real_diff_def]@add_ac) 1); 
qed "real_add_number_of_diff2";

Addsimps [real_add_number_of_left, real_mult_number_of_left,
          real_add_number_of_diff1, real_add_number_of_diff2];


(*"neg" is used in rewrite rules for binary comparisons*)
Goal "real (number_of v :: nat) = \
\       (if neg (number_of v) then 0 \
\        else (number_of v :: real))";
by (simp_tac
    (HOL_ss addsimps [nat_number_of_def, real_of_nat_real_of_int,
                      real_of_nat_neg_int, real_number_of,
                      real_numeral_0_eq_0 RS sym]) 1);
qed "real_of_nat_number_of";
Addsimps [real_of_nat_number_of];


(**** Simprocs for numeric literals ****)

(** For combine_numerals **)

Goal "i*u + (j*u + k) = (i+j)*u + (k::real)";
by (asm_simp_tac (simpset() addsimps [left_distrib] @ add_ac) 1);
qed "left_real_add_mult_distrib";


(** For cancel_numerals **)

val rel_iff_rel_0_rls = map (inst "b" "?u+?v")
                   [less_iff_diff_less_0, eq_iff_diff_eq_0, le_iff_diff_le_0] @
                 map (inst "b" "n")
                   [less_iff_diff_less_0, eq_iff_diff_eq_0, le_iff_diff_le_0];

Goal "!!i::real. (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]@
                                     add_ac@rel_iff_rel_0_rls) 1);
qed "real_eq_add_iff1";

Goal "!!i::real. (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]@
                                     add_ac@rel_iff_rel_0_rls) 1);
qed "real_eq_add_iff2";

Goal "!!i::real. (i*u + m < j*u + n) = ((i-j)*u + m < n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]@
                                     add_ac@rel_iff_rel_0_rls) 1);
qed "real_less_add_iff1";

Goal "!!i::real. (i*u + m < j*u + n) = (m < (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]@
                                     add_ac@rel_iff_rel_0_rls) 1);
qed "real_less_add_iff2";

Goal "!!i::real. (i*u + m <= j*u + n) = ((i-j)*u + m <= n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]@
                                     add_ac@rel_iff_rel_0_rls) 1);
qed "real_le_add_iff1";

Goal "!!i::real. (i*u + m <= j*u + n) = (m <= (j-i)*u + n)";
by (asm_simp_tac (simpset() addsimps [real_diff_def, left_distrib]
                                     @add_ac@rel_iff_rel_0_rls) 1);
qed "real_le_add_iff2";


Addsimps [real_numeral_0_eq_0, real_numeral_1_eq_1];


structure Real_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym];

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.realT $ HOLogic.mk_bin n;

(*Decodes a binary real constant, or 0, 1*)
val dest_numeral = Int_Numeral_Simprocs.dest_numeral;
val find_first_numeral = Int_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", HOLogic.realT --> HOLogic.realT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.realT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" HOLogic.realT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.realT;

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
val add_0s  = map rename_numerals [real_add_zero_left, real_add_zero_right];
val mult_1s = map rename_numerals [real_mult_1, real_mult_1_right] @
              [real_mult_minus1, real_mult_minus1_right];

(*To perform binary arithmetic*)
val bin_simps =
    [real_numeral_0_eq_0 RS sym, real_numeral_1_eq_1 RS sym,
     add_real_number_of, real_add_number_of_left, minus_real_number_of,
     diff_real_number_of, mult_real_number_of, real_mult_number_of_left] @
    bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [real_add_number_of_left, add_real_number_of];

(*To evaluate binary negations of coefficients*)
val real_minus_simps = NCons_simps @
                   [real_minus_1_eq_m1, minus_real_number_of,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [real_diff_def, minus_add_distrib, minus_minus];

(*to extract again any uncancelled minuses*)
val real_minus_from_mult_simps =
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val real_mult_minus_simps =
    [real_mult_assoc, minus_mult_left, real_minus_mult_commute];

(*Apply the given rewrite (if present) just once*)
fun trans_tac None      = all_tac
  | trans_tac (Some th) = ALLGOALS (rtac (th RS trans));

(*Final simplification: cancel + and *  *)
val simplify_meta_eq =
    Int_Numeral_Simprocs.simplify_meta_eq
         [add_0, add_0_right,
          mult_left_zero, mult_right_zero, mult_1, mult_1_right];

fun prep_simproc (name, pats, proc) =
  Simplifier.simproc (Theory.sign_of (the_context ())) name pats proc;

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         real_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@real_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps real_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.realT
  val bal_add1 = real_eq_add_iff1 RS trans
  val bal_add2 = real_eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.realT
  val bal_add1 = real_less_add_iff1 RS trans
  val bal_add2 = real_less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.realT
  val bal_add1 = real_le_add_iff1 RS trans
  val bal_add2 = real_le_add_iff2 RS trans
);

val cancel_numerals =
  map prep_simproc
   [("realeq_cancel_numerals",
     ["(l::real) + m = n", "(l::real) = m + n",
      "(l::real) - m = n", "(l::real) = m - n",
      "(l::real) * m = n", "(l::real) = m * n"],
     EqCancelNumerals.proc),
    ("realless_cancel_numerals",
     ["(l::real) + m < n", "(l::real) < m + n",
      "(l::real) - m < n", "(l::real) < m - n",
      "(l::real) * m < n", "(l::real) < m * n"],
     LessCancelNumerals.proc),
    ("realle_cancel_numerals",
     ["(l::real) + m <= n", "(l::real) <= m + n",
      "(l::real) - m <= n", "(l::real) <= m - n",
      "(l::real) * m <= n", "(l::real) <= m * n"],
     LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = left_real_add_mult_distrib RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                   diff_simps@real_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@real_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps real_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  =
        Int_Numeral_Simprocs.simplify_meta_eq (add_0s@mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc ("real_combine_numerals", ["(i::real) + j", "(i::real) - j"], CombineNumerals.proc);


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
        [real_mult_1, real_mult_1_right]
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure RealAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = real_numeral_0_eq_0
  val numeral_1_eq_1  = real_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure RealAbstractNumerals = AbstractNumeralsFun (RealAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("real_add_eval_numerals",
     ["(m::real) + 1", "(m::real) + number_of v"],
     RealAbstractNumerals.proc add_real_number_of),
    ("real_diff_eval_numerals",
     ["(m::real) - 1", "(m::real) - number_of v"],
     RealAbstractNumerals.proc diff_real_number_of),
    ("real_eq_eval_numerals",
     ["(m::real) = 0", "(m::real) = 1", "(m::real) = number_of v"],
     RealAbstractNumerals.proc eq_real_number_of),
    ("real_less_eval_numerals",
     ["(m::real) < 0", "(m::real) < 1", "(m::real) < number_of v"],
     RealAbstractNumerals.proc less_real_number_of),
    ("real_le_eval_numerals",
     ["(m::real) <= 0", "(m::real) <= 1", "(m::real) <= number_of v"],
     RealAbstractNumerals.proc le_real_number_of_eq_not_less)]

end;


Addsimprocs Real_Numeral_Simprocs.eval_numerals;
Addsimprocs Real_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Real_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

test "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::real)";

test "2*u = (u::real)";
test "(i + j + 12 + (k::real)) - 15 = y";
test "(i + j + 12 + (k::real)) - 5 = y";

test "y - b < (b::real)";
test "y - (3*b + c) < (b::real) - 2*c";

test "(2*x - (u*v) + y) - v*3*u = (w::real)";
test "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::real)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::real)";
test "u*v - (x*u*v + (u*v)*4 + y) = (w::real)";

test "(i + j + 12 + (k::real)) = u + 15 + y";
test "(i + j*2 + 12 + (k::real)) = j + 5 + y";

test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::real)";

test "a + -(b+c) + b = (d::real)";
test "a + -(b+c) - b = (d::real)";

(*negative numerals*)
test "(i + j + -2 + (k::real)) - (u + 5 + y) = zz";
test "(i + j + -3 + (k::real)) < u + 5 + y";
test "(i + j + 3 + (k::real)) < u + -6 + y";
test "(i + j + -12 + (k::real)) - 15 = y";
test "(i + j + 12 + (k::real)) - -15 = y";
test "(i + j + -12 + (k::real)) - -15 = y";
*)


(** Constant folding for real plus and times **)

(*We do not need
    structure Real_Plus_Assoc = Assoc_Fold (Real_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Real_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = HOLogic.realT
  val plus   = Const ("op *", [HOLogic.realT,HOLogic.realT] ---> HOLogic.realT)
  val add_ac = mult_ac
end;

structure Real_Times_Assoc = Assoc_Fold (Real_Times_Assoc_Data);

Addsimprocs [Real_Times_Assoc.conv];

(*Simplification of  x-y < 0, etc.*)
AddIffs [less_iff_diff_less_0 RS sym];
AddIffs [eq_iff_diff_eq_0 RS sym];
AddIffs [le_iff_diff_le_0 RS sym];

Addsimps [real_minus_1_eq_m1];
