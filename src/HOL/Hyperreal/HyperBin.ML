(*  Title:      HOL/Hyperreal/HyperBin.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Binary arithmetic for the hypreals (integer literals only).
*)

(** hypreal_of_real (coercion from int to real) **)

Goal "hypreal_of_real (number_of w) = number_of w";
by (simp_tac (simpset() addsimps [hypreal_number_of_def]) 1);
qed "hypreal_number_of";
Addsimps [hypreal_number_of];

Goalw [hypreal_number_of_def] "Numeral0 = (0::hypreal)";
by (Simp_tac 1);
qed "hypreal_numeral_0_eq_0";

Goalw [hypreal_number_of_def] "Numeral1 = (1::hypreal)";
by (Simp_tac 1);
qed "hypreal_numeral_1_eq_1";

(** Addition **)

Goal "(number_of v :: hypreal) + number_of v' = number_of (bin_add v v')";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def,
                      hypreal_of_real_add RS sym, add_real_number_of]) 1);
qed "add_hypreal_number_of";
Addsimps [add_hypreal_number_of];


(** Subtraction **)

Goalw [hypreal_number_of_def]
     "- (number_of w :: hypreal) = number_of (bin_minus w)";
by (simp_tac
    (HOL_ss addsimps [minus_real_number_of, hypreal_of_real_minus RS sym]) 1);
qed "minus_hypreal_number_of";
Addsimps [minus_hypreal_number_of];

Goalw [hypreal_number_of_def, hypreal_diff_def]
     "(number_of v :: hypreal) - number_of w = \
\     number_of (bin_add v (bin_minus w))";
by (Simp_tac 1);
qed "diff_hypreal_number_of";
Addsimps [diff_hypreal_number_of];


(** Multiplication **)

Goal "(number_of v :: hypreal) * number_of v' = number_of (bin_mult v v')";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def,
                      hypreal_of_real_mult RS sym, mult_real_number_of]) 1);
qed "mult_hypreal_number_of";
Addsimps [mult_hypreal_number_of];

Goal "(2::hypreal) = 1 + 1";
by (simp_tac (simpset() addsimps [hypreal_numeral_1_eq_1 RS sym]) 1);
val lemma = result();

(*For specialist use: NOT as default simprules*)
Goal "2 * z = (z+z::hypreal)";
by (simp_tac (simpset ()
              addsimps [lemma, left_distrib,
                        hypreal_numeral_1_eq_1]) 1);
qed "hypreal_mult_2";

Goal "z * 2 = (z+z::hypreal)";
by (stac hypreal_mult_commute 1 THEN rtac hypreal_mult_2 1);
qed "hypreal_mult_2_right";


(*** Comparisons ***)

(** Equals (=) **)

Goal "((number_of v :: hypreal) = number_of v') = \
\     iszero (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def,
                      hypreal_of_real_eq_iff, eq_real_number_of]) 1);
qed "eq_hypreal_number_of";
Addsimps [eq_hypreal_number_of];

(** Less-than (<) **)

(*"neg" is used in rewrite rules for binary comparisons*)
Goal "((number_of v :: hypreal) < number_of v') = \
\     neg (number_of (bin_add v (bin_minus v')))";
by (simp_tac
    (HOL_ss addsimps [hypreal_number_of_def, hypreal_of_real_less_iff,
                      less_real_number_of]) 1);
qed "less_hypreal_number_of";
Addsimps [less_hypreal_number_of];


(** Less-than-or-equals (<=) **)

Goal "(number_of x <= (number_of y::hypreal)) = \
\     (~ number_of y < (number_of x::hypreal))";
by (rtac (linorder_not_less RS sym) 1);
qed "le_hypreal_number_of_eq_not_less";
Addsimps [le_hypreal_number_of_eq_not_less];

(*** New versions of existing theorems involving 0, 1 ***)

Goal "- 1 = (-1::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_numeral_1_eq_1 RS sym]) 1);
qed "hypreal_minus_1_eq_m1";

(*Maps 0 to Numeral0 and 1 to Numeral1 and -(Numeral1) to -1*)
val hypreal_numeral_ss =
    real_numeral_ss addsimps [hypreal_numeral_0_eq_0 RS sym,
                              hypreal_numeral_1_eq_1 RS sym,
                              hypreal_minus_1_eq_m1];

fun rename_numerals th =
    asm_full_simplify hypreal_numeral_ss (Thm.transfer (the_context ()) th);


(** Simplification of arithmetic when nested to the right **)

Goal "number_of v + (number_of w + z) = (number_of(bin_add v w) + z::hypreal)";
by (asm_full_simp_tac (simpset() addsimps [add_assoc RS sym]) 1); 
qed "hypreal_add_number_of_left";

Goal "number_of v *(number_of w * z) = (number_of(bin_mult v w) * z::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_mult_assoc RS sym]) 1);
qed "hypreal_mult_number_of_left";

Goalw [hypreal_diff_def]
    "number_of v + (number_of w - c) = number_of(bin_add v w) - (c::hypreal)";
by (rtac hypreal_add_number_of_left 1);
qed "hypreal_add_number_of_diff1";

Goal "number_of v + (c - number_of w) = \
\     number_of (bin_add v (bin_minus w)) + (c::hypreal)";
by (stac (diff_hypreal_number_of RS sym) 1);
by (asm_full_simp_tac (HOL_ss addsimps [hypreal_diff_def]@add_ac) 1); 
qed "hypreal_add_number_of_diff2";

Addsimps [hypreal_add_number_of_left, hypreal_mult_number_of_left,
          hypreal_add_number_of_diff1, hypreal_add_number_of_diff2];


(**** Simprocs for numeric literals ****)

(** For combine_numerals **)

Goal "i*u + (j*u + k) = (i+j)*u + (k::hypreal)";
by (asm_simp_tac (simpset() addsimps [left_distrib] @ add_ac) 1);
qed "left_hypreal_add_mult_distrib";


(** For cancel_numerals **)

val rel_iff_rel_0_rls =
    map (inst "b" "?u+?v")
      [less_iff_diff_less_0, eq_iff_diff_eq_0,
       le_iff_diff_le_0] @
    map (inst "b" "n")
      [less_iff_diff_less_0, eq_iff_diff_eq_0,
       le_iff_diff_le_0];

Goal "!!i::hypreal. (i*u + m = j*u + n) = ((i-j)*u + m = n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                         add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_eq_add_iff1";

Goal "!!i::hypreal. (i*u + m = j*u + n) = (m = (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                         add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_eq_add_iff2";

Goal "!!i::hypreal. (i*u + m < j*u + n) = ((i-j)*u + m < n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                         add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_less_add_iff1";

Goal "!!i::hypreal. (i*u + m < j*u + n) = (m < (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                         add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_less_add_iff2";

Goal "!!i::hypreal. (i*u + m <= j*u + n) = ((i-j)*u + m <= n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                         add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_le_add_iff1";

Goal "!!i::hypreal. (i*u + m <= j*u + n) = (m <= (j-i)*u + n)";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, left_distrib]@
                        add_ac@rel_iff_rel_0_rls) 1);
qed "hypreal_le_add_iff2";

Goal "-1 * (z::hypreal) = -z";
by (simp_tac (simpset() addsimps [hypreal_minus_1_eq_m1 RS sym,
                                  hypreal_mult_minus_1]) 1);
qed "hypreal_mult_minus1";
Addsimps [hypreal_mult_minus1];

Goal "(z::hypreal) * -1 = -z";
by (stac hypreal_mult_commute 1 THEN rtac hypreal_mult_minus1 1);
qed "hypreal_mult_minus1_right";
Addsimps [hypreal_mult_minus1_right];


Addsimps [hypreal_numeral_0_eq_0, hypreal_numeral_1_eq_1];


structure Hyperreal_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [hypreal_numeral_0_eq_0 RS sym,
                    hypreal_numeral_1_eq_1 RS sym];

(*Utilities*)

val hyprealT = Type("HyperDef.hypreal",[]);

fun mk_numeral n = HOLogic.number_of_const hyprealT $ HOLogic.mk_bin n;

val dest_numeral = Real_Numeral_Simprocs.dest_numeral;

val find_first_numeral = Real_Numeral_Simprocs.find_first_numeral;

val zero = mk_numeral 0;
val mk_plus = Real_Numeral_Simprocs.mk_plus;

val uminus_const = Const ("uminus", hyprealT --> hyprealT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" hyprealT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" hyprealT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" hyprealT;

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
val add_0s = map rename_numerals
                 [hypreal_add_zero_left, hypreal_add_zero_right];
val mult_1s = map rename_numerals [hypreal_mult_1, hypreal_mult_1_right] @
              [hypreal_mult_minus1, hypreal_mult_minus1_right];

(*To perform binary arithmetic*)
val bin_simps =
    [hypreal_numeral_0_eq_0 RS sym, hypreal_numeral_1_eq_1 RS sym,
     add_hypreal_number_of, hypreal_add_number_of_left,
     minus_hypreal_number_of,
     diff_hypreal_number_of, mult_hypreal_number_of,
     hypreal_mult_number_of_left] @ bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [hypreal_add_number_of_left, add_hypreal_number_of];

(*To evaluate binary negations of coefficients*)
val hypreal_minus_simps = NCons_simps @
                   [hypreal_minus_1_eq_m1, minus_hypreal_number_of,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [hypreal_diff_def, minus_add_distrib, minus_minus];

(*push the unary minus down: - x * y = x * - y *)
val hypreal_minus_mult_eq_1_to_2 =
    [minus_mult_left RS sym, minus_mult_right] MRS trans
    |> standard;

(*to extract again any uncancelled minuses*)
val hypreal_minus_from_mult_simps =
    [minus_minus, minus_mult_left RS sym, minus_mult_right RS sym];

(*combine unary minus with numeric literals, however nested within a product*)
val hypreal_mult_minus_simps =
    [hypreal_mult_assoc, minus_mult_left, hypreal_minus_mult_eq_1_to_2];

(*Final simplification: cancel + and *  *)
val simplify_meta_eq =
    Int_Numeral_Simprocs.simplify_meta_eq
         [hypreal_add_zero_left, hypreal_add_zero_right,
          mult_zero_left, mult_zero_right, mult_1, mult_1_right];

val prep_simproc = Real_Numeral_Simprocs.prep_simproc;

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hypreal_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS
              (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                         add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" hyprealT
  val bal_add1 = hypreal_eq_add_iff1 RS trans
  val bal_add2 = hypreal_eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" hyprealT
  val bal_add1 = hypreal_less_add_iff1 RS trans
  val bal_add2 = hypreal_less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" hyprealT
  val bal_add1 = hypreal_le_add_iff1 RS trans
  val bal_add2 = hypreal_le_add_iff2 RS trans
);

val cancel_numerals =
  map prep_simproc
   [("hyprealeq_cancel_numerals",
     ["(l::hypreal) + m = n", "(l::hypreal) = m + n",
      "(l::hypreal) - m = n", "(l::hypreal) = m - n",
      "(l::hypreal) * m = n", "(l::hypreal) = m * n"],
     EqCancelNumerals.proc),
    ("hyprealless_cancel_numerals",
     ["(l::hypreal) + m < n", "(l::hypreal) < m + n",
      "(l::hypreal) - m < n", "(l::hypreal) < m - n",
      "(l::hypreal) * m < n", "(l::hypreal) < m * n"],
     LessCancelNumerals.proc),
    ("hyprealle_cancel_numerals",
     ["(l::hypreal) + m <= n", "(l::hypreal) <= m + n",
      "(l::hypreal) - m <= n", "(l::hypreal) <= m - n",
      "(l::hypreal) * m <= n", "(l::hypreal) <= m * n"],
     LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = left_hypreal_add_mult_distrib RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac         = Real_Numeral_Simprocs.trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps add_0s@mult_1s@diff_simps@
                                         hypreal_minus_simps@add_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@hypreal_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps hypreal_minus_from_mult_simps@
                                              add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc
    ("hypreal_combine_numerals", ["(i::hypreal) + j", "(i::hypreal) - j"], CombineNumerals.proc);


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
        [mult_1, mult_1_right]
        (([th, cancel_th]) MRS trans);

(*** Making constant folding work for 0 and 1 too ***)

structure HyperrealAbstractNumeralsData =
  struct
  val dest_eq         = HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
  val is_numeral      = Bin_Simprocs.is_numeral
  val numeral_0_eq_0  = hypreal_numeral_0_eq_0
  val numeral_1_eq_1  = hypreal_numeral_1_eq_1
  val prove_conv      = Bin_Simprocs.prove_conv_nohyps_novars
  fun norm_tac simps  = ALLGOALS (simp_tac (HOL_ss addsimps simps))
  val simplify_meta_eq = Bin_Simprocs.simplify_meta_eq
  end

structure HyperrealAbstractNumerals =
  AbstractNumeralsFun (HyperrealAbstractNumeralsData)

(*For addition, we already have rules for the operand 0.
  Multiplication is omitted because there are already special rules for
  both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
  For the others, having three patterns is a compromise between just having
  one (many spurious calls) and having nine (just too many!) *)
val eval_numerals =
  map prep_simproc
   [("hypreal_add_eval_numerals",
     ["(m::hypreal) + 1", "(m::hypreal) + number_of v"],
     HyperrealAbstractNumerals.proc add_hypreal_number_of),
    ("hypreal_diff_eval_numerals",
     ["(m::hypreal) - 1", "(m::hypreal) - number_of v"],
     HyperrealAbstractNumerals.proc diff_hypreal_number_of),
    ("hypreal_eq_eval_numerals",
     ["(m::hypreal) = 0", "(m::hypreal) = 1", "(m::hypreal) = number_of v"],
     HyperrealAbstractNumerals.proc eq_hypreal_number_of),
    ("hypreal_less_eval_numerals",
     ["(m::hypreal) < 0", "(m::hypreal) < 1", "(m::hypreal) < number_of v"],
     HyperrealAbstractNumerals.proc less_hypreal_number_of),
    ("hypreal_le_eval_numerals",
     ["(m::hypreal) <= 0", "(m::hypreal) <= 1", "(m::hypreal) <= number_of v"],
     HyperrealAbstractNumerals.proc le_hypreal_number_of_eq_not_less)]

end;

Addsimprocs Hyperreal_Numeral_Simprocs.eval_numerals;
Addsimprocs Hyperreal_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Hyperreal_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1));

test "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::hypreal)";
test "2*u = (u::hypreal)";
test "(i + j + 12 + (k::hypreal)) - 15 = y";
test "(i + j + 12 + (k::hypreal)) - 5 = y";

test "y - b < (b::hypreal)";
test "y - (3*b + c) < (b::hypreal) - 2*c";

test "(2*x - (u*v) + y) - v*3*u = (w::hypreal)";
test "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::hypreal)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::hypreal)";
test "u*v - (x*u*v + (u*v)*4 + y) = (w::hypreal)";

test "(i + j + 12 + (k::hypreal)) = u + 15 + y";
test "(i + j*2 + 12 + (k::hypreal)) = j + 5 + y";

test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::hypreal)";

test "a + -(b+c) + b = (d::hypreal)";
test "a + -(b+c) - b = (d::hypreal)";

(*negative numerals*)
test "(i + j + -2 + (k::hypreal)) - (u + 5 + y) = zz";
test "(i + j + -3 + (k::hypreal)) < u + 5 + y";
test "(i + j + 3 + (k::hypreal)) < u + -6 + y";
test "(i + j + -12 + (k::hypreal)) - 15 = y";
test "(i + j + 12 + (k::hypreal)) - -15 = y";
test "(i + j + -12 + (k::hypreal)) - -15 = y";
*)


(** Constant folding for hypreal plus and times **)

(*We do not need
    structure Hyperreal_Plus_Assoc = Assoc_Fold (Hyperreal_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Hyperreal_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref    = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = Hyperreal_Numeral_Simprocs.hyprealT
  val plus   = Const ("op *", [T,T] ---> T)
  val add_ac = mult_ac
end;

structure Hyperreal_Times_Assoc = Assoc_Fold (Hyperreal_Times_Assoc_Data);

Addsimprocs [Hyperreal_Times_Assoc.conv];

(*Simplification of  x-y < 0, etc.*)
AddIffs [less_iff_diff_less_0 RS sym];
AddIffs [eq_iff_diff_eq_0 RS sym];
AddIffs [le_iff_diff_le_0 RS sym];


(** number_of related to hypreal_of_real **)

Goal "(number_of w < hypreal_of_real z) = (number_of w < z)";
by (stac (hypreal_of_real_less_iff RS sym) 1);
by (Simp_tac 1);
qed "number_of_less_hypreal_of_real_iff";
Addsimps [number_of_less_hypreal_of_real_iff];

Goal "(number_of w <= hypreal_of_real z) = (number_of w <= z)";
by (stac (hypreal_of_real_le_iff RS sym) 1);
by (Simp_tac 1);
qed "number_of_le_hypreal_of_real_iff";
Addsimps [number_of_le_hypreal_of_real_iff];

Goal "(hypreal_of_real z = number_of w) = (z = number_of w)";
by (stac (hypreal_of_real_eq_iff RS sym) 1);
by (Simp_tac 1);
qed "hypreal_of_real_eq_number_of_iff";
Addsimps [hypreal_of_real_eq_number_of_iff];

Goal "(hypreal_of_real z < number_of w) = (z < number_of w)";
by (stac (hypreal_of_real_less_iff RS sym) 1);
by (Simp_tac 1);
qed "hypreal_of_real_less_number_of_iff";
Addsimps [hypreal_of_real_less_number_of_iff];

Goal "(hypreal_of_real z <= number_of w) = (z <= number_of w)";
by (stac (hypreal_of_real_le_iff RS sym) 1);
by (Simp_tac 1);
qed "hypreal_of_real_le_number_of_iff";
Addsimps [hypreal_of_real_le_number_of_iff];

(*As above, for the special case of zero*)
Addsimps
  (map (simplify (simpset()) o inst "w" "bin.Pls")
   [hypreal_of_real_eq_number_of_iff,
    hypreal_of_real_le_number_of_iff, hypreal_of_real_less_number_of_iff,
    number_of_le_hypreal_of_real_iff, number_of_less_hypreal_of_real_iff]);

(*As above, for the special case of one*)
Addsimps
  (map (simplify (simpset()) o inst "w" "bin.Pls BIT True")
   [hypreal_of_real_eq_number_of_iff,
    hypreal_of_real_le_number_of_iff, hypreal_of_real_less_number_of_iff,
    number_of_le_hypreal_of_real_iff, number_of_less_hypreal_of_real_iff]);

Addsimps [hypreal_minus_1_eq_m1];
