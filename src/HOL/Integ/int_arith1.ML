(*  Title:      HOL/Integ/int_arith1.ML
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow

Simprocs and decision procedure for linear arithmetic.
*)

(** Misc ML bindings **)

val NCons_Pls = thm"NCons_Pls";
val NCons_Min = thm"NCons_Min";
val NCons_BIT = thm"NCons_BIT";
val number_of_Pls = thm"number_of_Pls";
val number_of_Min = thm"number_of_Min";
val number_of_BIT = thm"number_of_BIT";
val bin_succ_Pls = thm"bin_succ_Pls";
val bin_succ_Min = thm"bin_succ_Min";
val bin_succ_BIT = thm"bin_succ_BIT";
val bin_pred_Pls = thm"bin_pred_Pls";
val bin_pred_Min = thm"bin_pred_Min";
val bin_pred_BIT = thm"bin_pred_BIT";
val bin_minus_Pls = thm"bin_minus_Pls";
val bin_minus_Min = thm"bin_minus_Min";
val bin_minus_BIT = thm"bin_minus_BIT";
val bin_add_Pls = thm"bin_add_Pls";
val bin_add_Min = thm"bin_add_Min";
val bin_mult_Pls = thm"bin_mult_Pls";
val bin_mult_Min = thm"bin_mult_Min";
val bin_mult_BIT = thm"bin_mult_BIT";

val zadd_ac = thms "Ring_and_Field.add_ac"
val zmult_ac = thms "Ring_and_Field.mult_ac"
val NCons_Pls_0 = thm"NCons_Pls_0";
val NCons_Pls_1 = thm"NCons_Pls_1";
val NCons_Min_0 = thm"NCons_Min_0";
val NCons_Min_1 = thm"NCons_Min_1";
val bin_succ_1 = thm"bin_succ_1";
val bin_succ_0 = thm"bin_succ_0";
val bin_pred_1 = thm"bin_pred_1";
val bin_pred_0 = thm"bin_pred_0";
val bin_minus_1 = thm"bin_minus_1";
val bin_minus_0 = thm"bin_minus_0";
val bin_add_BIT_11 = thm"bin_add_BIT_11";
val bin_add_BIT_10 = thm"bin_add_BIT_10";
val bin_add_BIT_0 = thm"bin_add_BIT_0";
val bin_add_Pls_right = thm"bin_add_Pls_right";
val bin_add_Min_right = thm"bin_add_Min_right";
val bin_add_BIT_BIT = thm"bin_add_BIT_BIT";
val bin_mult_1 = thm"bin_mult_1";
val bin_mult_0 = thm"bin_mult_0";
val number_of_NCons = thm"number_of_NCons";
val number_of_succ = thm"number_of_succ";
val number_of_pred = thm"number_of_pred";
val number_of_minus = thm"number_of_minus";
val number_of_add = thm"number_of_add";
val diff_number_of_eq = thm"diff_number_of_eq";
val number_of_mult = thm"number_of_mult";
val double_number_of_BIT = thm"double_number_of_BIT";
val int_numeral_0_eq_0 = thm"int_numeral_0_eq_0";
val int_numeral_1_eq_1 = thm"int_numeral_1_eq_1";
val zmult_minus1 = thm"zmult_minus1";
val zmult_minus1_right = thm"zmult_minus1_right";
val zminus_number_of_zmult = thm"zminus_number_of_zmult";
val zminus_1_eq_m1 = thm"zminus_1_eq_m1";
val zero_less_nat_eq = thm"zero_less_nat_eq";
val eq_number_of_eq = thm"eq_number_of_eq";
val iszero_number_of_Pls = thm"iszero_number_of_Pls";
val nonzero_number_of_Min = thm"nonzero_number_of_Min";
val iszero_number_of_BIT = thm"iszero_number_of_BIT";
val iszero_number_of_0 = thm"iszero_number_of_0";
val iszero_number_of_1 = thm"iszero_number_of_1";
val less_number_of_eq_neg = thm"less_number_of_eq_neg";
val not_neg_number_of_Pls = thm"not_neg_number_of_Pls";
val neg_number_of_Min = thm"neg_number_of_Min";
val neg_number_of_BIT = thm"neg_number_of_BIT";
val le_number_of_eq_not_less = thm"le_number_of_eq_not_less";
val zabs_number_of = thm"zabs_number_of";
val zabs_0 = thm"zabs_0";
val zabs_1 = thm"zabs_1";
val number_of_reorient = thm"number_of_reorient";
val add_number_of_left = thm"add_number_of_left";
val mult_number_of_left = thm"mult_number_of_left";
val add_number_of_diff1 = thm"add_number_of_diff1";
val add_number_of_diff2 = thm"add_number_of_diff2";
val less_iff_diff_less_0 = thm"less_iff_diff_less_0";
val eq_iff_diff_eq_0 = thm"eq_iff_diff_eq_0";
val le_iff_diff_le_0 = thm"le_iff_diff_le_0";

val bin_mult_simps = thms"bin_mult_simps";
val NCons_simps = thms"NCons_simps";
val bin_arith_extra_simps = thms"bin_arith_extra_simps";
val bin_arith_simps = thms"bin_arith_simps";
val bin_rel_simps = thms"bin_rel_simps";

val zless_imp_add1_zle = thm "zless_imp_add1_zle";

val combine_common_factor = thm"combine_common_factor";
val eq_add_iff1 = thm"eq_add_iff1";
val eq_add_iff2 = thm"eq_add_iff2";
val less_add_iff1 = thm"less_add_iff1";
val less_add_iff2 = thm"less_add_iff2";
val le_add_iff1 = thm"le_add_iff1";
val le_add_iff2 = thm"le_add_iff2";


structure Bin_Simprocs =
  struct
  fun prove_conv tacs sg (hyps: thm list) xs (t, u) =
    if t aconv u then None
    else
      let val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))
      in Some (Tactic.prove sg xs [] eq (K (EVERY tacs))) end

  fun prove_conv_nohyps tacs sg = prove_conv tacs sg [];
  fun prove_conv_nohyps_novars tacs sg = prove_conv tacs sg [] [];

  fun prep_simproc (name, pats, proc) =
    Simplifier.simproc (Theory.sign_of (the_context())) name pats proc;

  fun is_numeral (Const("Numeral.number_of", _) $ w) = true
    | is_numeral _ = false

  fun simplify_meta_eq f_number_of_eq f_eq =
      mk_meta_eq ([f_eq, f_number_of_eq] MRS trans)

  structure IntAbstractNumeralsData =
    struct
    val dest_eq		= HOLogic.dest_eq o HOLogic.dest_Trueprop o concl_of
    val is_numeral	= is_numeral
    val numeral_0_eq_0    = int_numeral_0_eq_0
    val numeral_1_eq_1    = int_numeral_1_eq_1
    val prove_conv	= prove_conv_nohyps_novars
    fun norm_tac simps	= ALLGOALS (simp_tac (HOL_ss addsimps simps))
    val simplify_meta_eq  = simplify_meta_eq 
    end

  structure IntAbstractNumerals = AbstractNumeralsFun (IntAbstractNumeralsData)


  (*For addition, we already have rules for the operand 0.
    Multiplication is omitted because there are already special rules for 
    both 0 and 1 as operands.  Unary minus is trivial, just have - 1 = -1.
    For the others, having three patterns is a compromise between just having
    one (many spurious calls) and having nine (just too many!) *)
  val eval_numerals = 
    map prep_simproc
     [("int_add_eval_numerals",
       ["(m::int) + 1", "(m::int) + number_of v"], 
       IntAbstractNumerals.proc (number_of_add RS sym)),
      ("int_diff_eval_numerals",
       ["(m::int) - 1", "(m::int) - number_of v"], 
       IntAbstractNumerals.proc diff_number_of_eq),
      ("int_eq_eval_numerals",
       ["(m::int) = 0", "(m::int) = 1", "(m::int) = number_of v"], 
       IntAbstractNumerals.proc eq_number_of_eq),
      ("int_less_eval_numerals",
       ["(m::int) < 0", "(m::int) < 1", "(m::int) < number_of v"], 
       IntAbstractNumerals.proc less_number_of_eq_neg),
      ("int_le_eval_numerals",
       ["(m::int) <= 0", "(m::int) <= 1", "(m::int) <= number_of v"],
       IntAbstractNumerals.proc le_number_of_eq_not_less)]

  (*reorientation simprules using ==, for the following simproc*)
  val meta_zero_reorient = zero_reorient RS eq_reflection
  val meta_one_reorient = one_reorient RS eq_reflection
  val meta_number_of_reorient = number_of_reorient RS eq_reflection

  (*reorientation simplification procedure: reorients (polymorphic) 
    0 = x, 1 = x, nnn = x provided x isn't 0, 1 or a numeral.*)
  fun reorient_proc sg _ (_ $ t $ u) =
    case u of
	Const("0", _) => None
      | Const("1", _) => None
      | Const("Numeral.number_of", _) $ _ => None
      | _ => Some (case t of
		  Const("0", _) => meta_zero_reorient
		| Const("1", _) => meta_one_reorient
		| Const("Numeral.number_of", _) $ _ => meta_number_of_reorient)

  val reorient_simproc = 
      prep_simproc ("reorient_simproc", ["0=x", "1=x", "number_of w = x"], reorient_proc)

  end;


Addsimprocs Bin_Simprocs.eval_numerals;
Addsimprocs [Bin_Simprocs.reorient_simproc];


structure Int_Numeral_Simprocs =
struct

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic in simprocs
  isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [int_numeral_0_eq_0 RS sym, int_numeral_1_eq_1 RS sym];
val numeral_sym_ss = HOL_ss addsimps numeral_syms;

fun rename_numerals th =
    simplify numeral_sym_ss (Thm.transfer (the_context ()) th);

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.intT $ HOLogic.mk_bin n;

(*Decodes a binary INTEGER*)
fun dest_numeral (Const("0", _)) = 0
  | dest_numeral (Const("1", _)) = 1
  | dest_numeral (Const("Numeral.number_of", _) $ w) =
     (HOLogic.dest_binum w
      handle TERM _ => raise TERM("Int_Numeral_Simprocs.dest_numeral:1", [w]))
  | dest_numeral t = raise TERM("Int_Numeral_Simprocs.dest_numeral:2", [t]);

fun find_first_numeral past (t::terms) =
        ((dest_numeral t, rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

val uminus_const = Const ("uminus", HOLogic.intT --> HOLogic.intT);

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.intT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("op +", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("op -", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else uminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop "op -";
val dest_diff = HOLogic.dest_bin "op -" HOLogic.intT;

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.intT;

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
val add_0s =  map rename_numerals [zadd_0, zadd_0_right];
val mult_1s = map rename_numerals [zmult_1, zmult_1_right] @
              [zmult_minus1, zmult_minus1_right];

(*To perform binary arithmetic.  The "left" rewriting handles patterns
  created by the simprocs, such as 3 * (5 * x). *)
val bin_simps = [int_numeral_0_eq_0 RS sym, int_numeral_1_eq_1 RS sym,
                 add_number_of_left, mult_number_of_left] @
                bin_arith_simps @ bin_rel_simps;

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_bin_simps = 
    bin_simps \\ [add_number_of_left, number_of_add RS sym];

(*To evaluate binary negations of coefficients*)
val zminus_simps = NCons_simps @
                   [zminus_1_eq_m1, number_of_minus RS sym,
                    bin_minus_1, bin_minus_0, bin_minus_Pls, bin_minus_Min,
                    bin_pred_1, bin_pred_0, bin_pred_Pls, bin_pred_Min];

(*To let us treat subtraction as addition*)
val diff_simps = [zdiff_def, zminus_zadd_distrib, zminus_zminus];

(*push the unary minus down: - x * y = x * - y *)
val int_minus_mult_eq_1_to_2 =
    [zmult_zminus, zmult_zminus_right RS sym] MRS trans |> standard;

(*to extract again any uncancelled minuses*)
val int_minus_from_mult_simps =
    [zminus_zminus, zmult_zminus, zmult_zminus_right];

(*combine unary minus with numeric literals, however nested within a product*)
val int_mult_minus_simps =
    [zmult_assoc, zmult_zminus RS sym, int_minus_mult_eq_1_to_2];

(*Apply the given rewrite (if present) just once*)
fun trans_tac None      = all_tac
  | trans_tac (Some th) = ALLGOALS (rtac (th RS trans));

fun simplify_meta_eq rules =
    simplify (HOL_basic_ss addeqcongs[eq_cong2] addsimps rules)
    o mk_meta_eq;

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                         diff_simps@zminus_simps@zadd_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@int_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps int_minus_from_mult_simps@
                                              zadd_ac@zmult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq (add_0s@mult_1s)
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.intT
  val bal_add1 = eq_add_iff1 RS trans
  val bal_add2 = eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.intT
  val bal_add1 = less_add_iff1 RS trans
  val bal_add2 = less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.intT
  val bal_add1 = le_add_iff1 RS trans
  val bal_add2 = le_add_iff2 RS trans
);

val cancel_numerals =
  map Bin_Simprocs.prep_simproc
   [("inteq_cancel_numerals",
     ["(l::int) + m = n", "(l::int) = m + n",
      "(l::int) - m = n", "(l::int) = m - n",
      "(l::int) * m = n", "(l::int) = m * n"],
     EqCancelNumerals.proc),
    ("intless_cancel_numerals",
     ["(l::int) + m < n", "(l::int) < m + n",
      "(l::int) - m < n", "(l::int) < m - n",
      "(l::int) * m < n", "(l::int) < m * n"],
     LessCancelNumerals.proc),
    ("intle_cancel_numerals",
     ["(l::int) + m <= n", "(l::int) <= m + n",
      "(l::int) - m <= n", "(l::int) <= m - n",
      "(l::int) * m <= n", "(l::int) <= m * n"],
     LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = combine_common_factor RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac          = trans_tac
  val norm_tac =
     ALLGOALS (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                         diff_simps@zminus_simps@zadd_ac))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps non_add_bin_simps@int_mult_minus_simps))
     THEN ALLGOALS (simp_tac (HOL_ss addsimps int_minus_from_mult_simps@
                                              zadd_ac@zmult_ac))
  val numeral_simp_tac  = ALLGOALS
                    (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq (add_0s@mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  Bin_Simprocs.prep_simproc
    ("int_combine_numerals", ["(i::int) + j", "(i::int) - j"], CombineNumerals.proc);

end;

Addsimprocs Int_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Int_Numeral_Simprocs.combine_numerals];

(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s, by (Simp_tac 1));

test "l + 2 + 2 + 2 + (l + 2) + (oo + 2) = (uu::int)";

test "2*u = (u::int)";
test "(i + j + 12 + (k::int)) - 15 = y";
test "(i + j + 12 + (k::int)) - 5 = y";

test "y - b < (b::int)";
test "y - (3*b + c) < (b::int) - 2*c";

test "(2*x - (u*v) + y) - v*3*u = (w::int)";
test "(2*x*u*v + (u*v)*4 + y) - v*u*4 = (w::int)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::int)";
test "u*v - (x*u*v + (u*v)*4 + y) = (w::int)";

test "(i + j + 12 + (k::int)) = u + 15 + y";
test "(i + j*2 + 12 + (k::int)) = j + 5 + y";

test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::int)";

test "a + -(b+c) + b = (d::int)";
test "a + -(b+c) - b = (d::int)";

(*negative numerals*)
test "(i + j + -2 + (k::int)) - (u + 5 + y) = zz";
test "(i + j + -3 + (k::int)) < u + 5 + y";
test "(i + j + 3 + (k::int)) < u + -6 + y";
test "(i + j + -12 + (k::int)) - 15 = y";
test "(i + j + 12 + (k::int)) - -15 = y";
test "(i + j + -12 + (k::int)) - -15 = y";
*)


(** Constant folding for integer plus and times **)

(*We do not need
    structure Nat_Plus_Assoc = Assoc_Fold (Nat_Plus_Assoc_Data);
    structure Int_Plus_Assoc = Assoc_Fold (Int_Plus_Assoc_Data);
  because combine_numerals does the same thing*)

structure Int_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = HOLogic.intT
  val plus   = Const ("op *", [HOLogic.intT,HOLogic.intT] ---> HOLogic.intT);
  val add_ac = zmult_ac
end;

structure Int_Times_Assoc = Assoc_Fold (Int_Times_Assoc_Data);

Addsimprocs [Int_Times_Assoc.conv];


(** The same for the naturals **)

structure Nat_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss                = HOL_ss
  val eq_reflection     = eq_reflection
  val sg_ref = Sign.self_ref (Theory.sign_of (the_context ()))
  val T      = HOLogic.natT
  val plus   = Const ("op *", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = mult_ac
end;

structure Nat_Times_Assoc = Assoc_Fold (Nat_Times_Assoc_Data);

Addsimprocs [Nat_Times_Assoc.conv];


(*** decision procedure for linear arithmetic ***)

(*---------------------------------------------------------------------------*)
(* Linear arithmetic                                                         *)
(*---------------------------------------------------------------------------*)

(*
Instantiation of the generic linear arithmetic package for int.
*)

(* Update parameters of arithmetic prover *)
local

(* reduce contradictory <= to False *)
val add_rules =
    simp_thms @ bin_arith_simps @ bin_rel_simps @
    [int_numeral_0_eq_0, int_numeral_1_eq_1,
     zminus_0, zdiff_def,
     zadd_zminus_inverse, zadd_zminus_inverse2,
     zmult_0, zmult_0_right,
     zmult_1, zmult_1_right,
     zmult_zminus, zmult_zminus_right,
     zminus_zadd_distrib, zminus_zminus, zmult_assoc,
     int_0, int_1, int_Suc, zadd_int RS sym, zmult_int RS sym];

val simprocs = [Int_Times_Assoc.conv, Int_Numeral_Simprocs.combine_numerals]@
               Int_Numeral_Simprocs.cancel_numerals @
               Bin_Simprocs.eval_numerals;

in

val int_arith_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = mult_mono_thms,
    inj_thms = [zle_int RS iffD2,int_int_eq RS iffD2] @ inj_thms,
    lessD = lessD @ [zless_imp_add1_zle],
    simpset = simpset addsimps add_rules
                      addsimprocs simprocs
                      addcongs [if_weak_cong]}),
  arith_inj_const ("IntDef.int", HOLogic.natT --> HOLogic.intT),
  arith_discrete ("IntDef.int", true)];

end;

val fast_int_arith_simproc =
  Simplifier.simproc (Theory.sign_of (the_context()))
  "fast_int_arith" ["(m::int) < n","(m::int) <= n", "(m::int) = n"] Fast_Arith.lin_arith_prover;

Addsimprocs [fast_int_arith_simproc]


(* Some test data
Goal "!!a::int. [| a <= b; c <= d; x+y<z |] ==> a+c <= b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a-d+ 2 <= b+(-c)";
by (fast_arith_tac 1);
Goal "!!a::int. [| a < b; c < d |] ==> a+c+ 1 < b+d";
by (fast_arith_tac 1);
Goal "!!a::int. [| a <= b; b+b <= c |] ==> a+a <= c";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b <= i+j; a<=b; i<=j |] \
\     ==> a+a <= j+j";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b < i+j; a<b; i<j |] \
\     ==> a+a - - -1 < j+j - 3";
by (fast_arith_tac 1);
Goal "!!a::int. a+b+c <= i+j+k & a<=b & b<=c & i<=j & j<=k --> a+a+a <= k+k+k";
by (arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a <= l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a <= l+l+l+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a <= l+l+l+l+i";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> a+a+a+a+a+a <= l+l+l+l+i+l";
by (fast_arith_tac 1);
Goal "!!a::int. [| a+b+c+d <= i+j+k+l; a<=b; b<=c; c<=d; i<=j; j<=k; k<=l |] \
\     ==> 6*a <= 5*l+i";
by (fast_arith_tac 1);
*)
