(*  Title:      HOL/nat_simprocs.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Simprocs for nat numerals.
*)

val Let_number_of = thm"Let_number_of";
val Let_0 = thm"Let_0";
val Let_1 = thm"Let_1";

structure Nat_Numeral_Simprocs =
struct

(*Maps n to #n for n = 0, 1, 2*)
val numeral_syms =
       [nat_numeral_0_eq_0 RS sym, nat_numeral_1_eq_1 RS sym, numeral_2_eq_2 RS sym];
val numeral_sym_ss = HOL_ss addsimps numeral_syms;

fun rename_numerals th =
    simplify numeral_sym_ss (Thm.transfer (the_context ()) th);

(*Utilities*)

fun mk_numeral n = HOLogic.number_of_const HOLogic.natT $ HOLogic.mk_bin n;

(*Decodes a unary or binary numeral to a NATURAL NUMBER*)
fun dest_numeral (Const ("0", _)) = 0
  | dest_numeral (Const ("Suc", _) $ t) = 1 + dest_numeral t
  | dest_numeral (Const("Numeral.number_of", _) $ w) =
      (BasisLibrary.Int.max (0, HOLogic.dest_binum w)
       handle TERM _ => raise TERM("Nat_Numeral_Simprocs.dest_numeral:1", [w]))
  | dest_numeral t = raise TERM("Nat_Numeral_Simprocs.dest_numeral:2", [t]);

fun find_first_numeral past (t::terms) =
        ((dest_numeral t, t, rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = HOLogic.mk_binop "op +";

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = HOLogic.zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

(*extract the outer Sucs from a term and convert them to a binary numeral*)
fun dest_Sucs (k, Const ("Suc", _) $ t) = dest_Sucs (k+1, t)
  | dest_Sucs (0, t) = t
  | dest_Sucs (k, t) = mk_plus (mk_numeral k, t);

fun dest_sum t =
      let val (t,u) = dest_plus t
      in  dest_sum t @ dest_sum u  end
      handle TERM _ => [t];

fun dest_Sucs_sum t = dest_sum (dest_Sucs (0,t));


(** Other simproc items **)

val trans_tac = Int_Numeral_Simprocs.trans_tac;

val bin_simps =
     [nat_numeral_0_eq_0 RS sym, nat_numeral_1_eq_1 RS sym,
      add_nat_number_of, nat_number_of_add_left, 
      diff_nat_number_of, le_number_of_eq_not_less,
      mult_nat_number_of, nat_number_of_mult_left, 
      less_nat_number_of, 
      Let_number_of, nat_number_of] @
     bin_arith_simps @ bin_rel_simps;

fun prep_simproc (name, pats, proc) =
  Simplifier.simproc (Theory.sign_of (the_context ())) name pats proc;


(*** CancelNumerals simprocs ***)

val one = mk_numeral 1;
val mk_times = HOLogic.mk_binop "op *";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin "op *" HOLogic.natT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k,t) = mk_times (mk_numeral k, t);

(*Express t as a product of (possibly) a numeral with other factors, sorted*)
fun dest_coeff t =
    let val ts = sort Term.term_ord (dest_prod t)
        val (n, _, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, one, ts)
    in (n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff t
        in  if u aconv u' then (n, rev past @ terms)
                          else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify 1*n and n*1 to n*)
val add_0s  = map rename_numerals [add_0, add_0_right];
val mult_1s = map rename_numerals [thm"nat_mult_1", thm"nat_mult_1_right"];

(*Final simplification: cancel + and *; replace Numeral0 by 0 and Numeral1 by 1*)

(*And these help the simproc return False when appropriate, which helps
  the arith prover.*)
val contra_rules = [add_Suc, add_Suc_right, Zero_not_Suc, Suc_not_Zero,
                    le_0_eq];

val simplify_meta_eq =
    Int_Numeral_Simprocs.simplify_meta_eq
        ([nat_numeral_0_eq_0, numeral_1_eq_Suc_0, add_0, add_0_right,
          mult_0, mult_0_right, mult_1, mult_1_right] @ contra_rules);


(** Restricted version of dest_Sucs_sum for nat_combine_numerals:
    Simprocs never apply unless the original expression contains at least one
    numeral in a coefficient position.
**)

fun ignore_Sucs (Const ("Suc", _) $ t) = ignore_Sucs t
  | ignore_Sucs t = t;

fun is_numeral (Const("Numeral.number_of", _) $ w) = true
  | is_numeral _ = false;

fun prod_has_numeral t = exists is_numeral (dest_prod t);

fun restricted_dest_Sucs_sum t =
    if exists prod_has_numeral (dest_sum (ignore_Sucs t))
    then dest_Sucs_sum t
    else raise TERM("Nat_Numeral_Simprocs.restricted_dest_Sucs_sum", [t]);


(*** Applying CancelNumeralsFun ***)

structure CancelNumeralsCommon =
  struct
  val mk_sum            = (fn T:typ => mk_sum)
  val dest_sum          = dest_Sucs_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first_coeff  = find_first_coeff []
  val trans_tac          = trans_tac
  val norm_tac = ALLGOALS
                   (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                                [Suc_eq_add_numeral_1] @ add_ac))
                 THEN ALLGOALS (simp_tac
                                (HOL_ss addsimps bin_simps@add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT
  val bal_add1 = nat_eq_add_iff1 RS trans
  val bal_add2 = nat_eq_add_iff2 RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT
  val bal_add1 = nat_less_add_iff1 RS trans
  val bal_add2 = nat_less_add_iff2 RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT
  val bal_add1 = nat_le_add_iff1 RS trans
  val bal_add2 = nat_le_add_iff2 RS trans
);

structure DiffCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "op -"
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT
  val bal_add1 = nat_diff_add_eq1 RS trans
  val bal_add2 = nat_diff_add_eq2 RS trans
);


val cancel_numerals =
  map prep_simproc
   [("nateq_cancel_numerals",
     ["(l::nat) + m = n", "(l::nat) = m + n",
      "(l::nat) * m = n", "(l::nat) = m * n",
      "Suc m = n", "m = Suc n"],
     EqCancelNumerals.proc),
    ("natless_cancel_numerals",
     ["(l::nat) + m < n", "(l::nat) < m + n",
      "(l::nat) * m < n", "(l::nat) < m * n",
      "Suc m < n", "m < Suc n"],
     LessCancelNumerals.proc),
    ("natle_cancel_numerals",
     ["(l::nat) + m <= n", "(l::nat) <= m + n",
      "(l::nat) * m <= n", "(l::nat) <= m * n",
      "Suc m <= n", "m <= Suc n"],
     LeCancelNumerals.proc),
    ("natdiff_cancel_numerals",
     ["((l::nat) + m) - n", "(l::nat) - (m + n)",
      "(l::nat) * m - n", "(l::nat) - m * n",
      "Suc m - n", "m - Suc n"],
     DiffCancelNumerals.proc)];


(*** Applying CombineNumeralsFun ***)

structure CombineNumeralsData =
  struct
  val add               = op + : int*int -> int
  val mk_sum            = (fn T:typ => long_mk_sum)  (*to work for 2*x + 3*x *)
  val dest_sum          = restricted_dest_Sucs_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val left_distrib      = left_add_mult_distrib RS trans
  val prove_conv        = Bin_Simprocs.prove_conv_nohyps
  val trans_tac          = trans_tac
  val norm_tac = ALLGOALS
                   (simp_tac (HOL_ss addsimps numeral_syms@add_0s@mult_1s@
                              [Suc_eq_add_numeral_1] @ add_ac))
                 THEN ALLGOALS (simp_tac
                                (HOL_ss addsimps bin_simps@add_ac@mult_ac))
  val numeral_simp_tac  = ALLGOALS
                (simp_tac (HOL_ss addsimps add_0s@bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc ("nat_combine_numerals", ["(i::nat) + j", "Suc (i + j)"], CombineNumerals.proc);


(*** Applying CancelNumeralFactorFun ***)

structure CancelNumeralFactorCommon =
  struct
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val trans_tac         = trans_tac
  val norm_tac = ALLGOALS
                    (simp_tac (HOL_ss addsimps [Suc_eq_add_numeral_1]@mult_1s))
                 THEN ALLGOALS (simp_tac (HOL_ss addsimps bin_simps))
                 THEN ALLGOALS (simp_tac (HOL_ss addsimps mult_ac))
  val numeral_simp_tac  = ALLGOALS (simp_tac (HOL_ss addsimps bin_simps))
  val simplify_meta_eq  = simplify_meta_eq
  end

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.natT
  val cancel = nat_mult_div_cancel1 RS trans
  val neg_exchanges = false
)

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT
  val cancel = nat_mult_eq_cancel1 RS trans
  val neg_exchanges = false
)

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT
  val cancel = nat_mult_less_cancel1 RS trans
  val neg_exchanges = true
)

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT
  val cancel = nat_mult_le_cancel1 RS trans
  val neg_exchanges = true
)

val cancel_numeral_factors =
  map prep_simproc
   [("nateq_cancel_numeral_factors",
     ["(l::nat) * m = n", "(l::nat) = m * n"],
     EqCancelNumeralFactor.proc),
    ("natless_cancel_numeral_factors",
     ["(l::nat) * m < n", "(l::nat) < m * n"],
     LessCancelNumeralFactor.proc),
    ("natle_cancel_numeral_factors",
     ["(l::nat) * m <= n", "(l::nat) <= m * n"],
     LeCancelNumeralFactor.proc),
    ("natdiv_cancel_numeral_factors",
     ["((l::nat) * m) div n", "(l::nat) div (m * n)"],
     DivCancelNumeralFactor.proc)];



(*** Applying ExtractCommonTermFun ***)

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
    Int_Numeral_Simprocs.simplify_meta_eq  [zmult_1, zmult_1_right]
        (([th, cancel_th]) MRS trans);

structure CancelFactorCommon =
  struct
  val mk_sum            = (fn T:typ => long_mk_prod)
  val dest_sum          = dest_prod
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first        = find_first []
  val trans_tac         = trans_tac
  val norm_tac = ALLGOALS (simp_tac (HOL_ss addsimps mult_1s@mult_ac))
  end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT
  val simplify_meta_eq  = cancel_simplify_meta_eq nat_mult_eq_cancel_disj
);

structure LessCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <"
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT
  val simplify_meta_eq  = cancel_simplify_meta_eq nat_mult_less_cancel_disj
);

structure LeCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binrel "op <="
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT
  val simplify_meta_eq  = cancel_simplify_meta_eq nat_mult_le_cancel_disj
);

structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val prove_conv = Bin_Simprocs.prove_conv
  val mk_bal   = HOLogic.mk_binop "Divides.op div"
  val dest_bal = HOLogic.dest_bin "Divides.op div" HOLogic.natT
  val simplify_meta_eq  = cancel_simplify_meta_eq nat_mult_div_cancel_disj
);

val cancel_factor =
  map prep_simproc
   [("nat_eq_cancel_factor",
     ["(l::nat) * m = n", "(l::nat) = m * n"],
     EqCancelFactor.proc),
    ("nat_less_cancel_factor",
     ["(l::nat) * m < n", "(l::nat) < m * n"],
     LessCancelFactor.proc),
    ("nat_le_cancel_factor",
     ["(l::nat) * m <= n", "(l::nat) <= m * n"],
     LeCancelFactor.proc),
    ("nat_divide_cancel_factor",
     ["((l::nat) * m) div n", "(l::nat) div (m * n)"],
     DivideCancelFactor.proc)];

end;


Addsimprocs Nat_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Nat_Numeral_Simprocs.combine_numerals];
Addsimprocs Nat_Numeral_Simprocs.cancel_numeral_factors;
Addsimprocs Nat_Numeral_Simprocs.cancel_factor;


(*examples:
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Simp_tac 1));

(*cancel_numerals*)
test "l +( 2) + (2) + 2 + (l + 2) + (oo  + 2) = (uu::nat)";
test "(2*length xs < 2*length xs + j)";
test "(2*length xs < length xs * 2 + j)";
test "2*u = (u::nat)";
test "2*u = Suc (u)";
test "(i + j + 12 + (k::nat)) - 15 = y";
test "(i + j + 12 + (k::nat)) - 5 = y";
test "Suc u - 2 = y";
test "Suc (Suc (Suc u)) - 2 = y";
test "(i + j + 2 + (k::nat)) - 1 = y";
test "(i + j + 1 + (k::nat)) - 2 = y";

test "(2*x + (u*v) + y) - v*3*u = (w::nat)";
test "(2*x*u*v + 5 + (u*v)*4 + y) - v*u*4 = (w::nat)";
test "(2*x*u*v + (u*v)*4 + y) - v*u = (w::nat)";
test "Suc (Suc (2*x*u*v + u*4 + y)) - u = w";
test "Suc ((u*v)*4) - v*3*u = w";
test "Suc (Suc ((u*v)*3)) - v*3*u = w";

test "(i + j + 12 + (k::nat)) = u + 15 + y";
test "(i + j + 32 + (k::nat)) - (u + 15 + y) = zz";
test "(i + j + 12 + (k::nat)) = u + 5 + y";
(*Suc*)
test "(i + j + 12 + k) = Suc (u + y)";
test "Suc (Suc (Suc (Suc (Suc (u + y))))) <= ((i + j) + 41 + k)";
test "(i + j + 5 + k) < Suc (Suc (Suc (Suc (Suc (u + y)))))";
test "Suc (Suc (Suc (Suc (Suc (u + y))))) - 5 = v";
test "(i + j + 5 + k) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (u + y)))))))";
test "2*y + 3*z + 2*u = Suc (u)";
test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = Suc (u)";
test "2*y + 3*z + 6*w + 2*y + 3*z + 2*u = 2*y' + 3*z' + 6*w' + 2*y' + 3*z' + u + (vv::nat)";
test "6 + 2*y + 3*z + 4*u = Suc (vv + 2*u + z)";
test "(2*n*m) < (3*(m*n)) + (u::nat)";

(*negative numerals: FAIL*)
test "(i + j + -23 + (k::nat)) < u + 15 + y";
test "(i + j + 3 + (k::nat)) < u + -15 + y";
test "(i + j + -12 + (k::nat)) - 15 = y";
test "(i + j + 12 + (k::nat)) - -15 = y";
test "(i + j + -12 + (k::nat)) - -15 = y";

(*combine_numerals*)
test "k + 3*k = (u::nat)";
test "Suc (i + 3) = u";
test "Suc (i + j + 3 + k) = u";
test "k + j + 3*k + j = (u::nat)";
test "Suc (j*i + i + k + 5 + 3*k + i*j*4) = (u::nat)";
test "(2*n*m) + (3*(m*n)) = (u::nat)";
(*negative numerals: FAIL*)
test "Suc (i + j + -3 + k) = u";

(*cancel_numeral_factors*)
test "9*x = 12 * (y::nat)";
test "(9*x) div (12 * (y::nat)) = z";
test "9*x < 12 * (y::nat)";
test "9*x <= 12 * (y::nat)";

(*cancel_factor*)
test "x*k = k*(y::nat)";
test "k = k*(y::nat)";
test "a*(b*c) = (b::nat)";
test "a*(b*c) = d*(b::nat)*(x*a)";

test "x*k < k*(y::nat)";
test "k < k*(y::nat)";
test "a*(b*c) < (b::nat)";
test "a*(b*c) < d*(b::nat)*(x*a)";

test "x*k <= k*(y::nat)";
test "k <= k*(y::nat)";
test "a*(b*c) <= (b::nat)";
test "a*(b*c) <= d*(b::nat)*(x*a)";

test "(x*k) div (k*(y::nat)) = (uu::nat)";
test "(k) div (k*(y::nat)) = (uu::nat)";
test "(a*(b*c)) div ((b::nat)) = (uu::nat)";
test "(a*(b*c)) div (d*(b::nat)*(x*a)) = (uu::nat)";
*)


(*** Prepare linear arithmetic for nat numerals ***)

local

(* reduce contradictory <= to False *)
val add_rules =
  [thm "Let_number_of", Let_0, Let_1, nat_0, nat_1,
   add_nat_number_of, diff_nat_number_of, mult_nat_number_of,
   eq_nat_number_of, less_nat_number_of, le_number_of_eq_not_less,
   le_Suc_number_of,le_number_of_Suc,
   less_Suc_number_of,less_number_of_Suc,
   Suc_eq_number_of,eq_number_of_Suc,
   mult_Suc, mult_Suc_right,
   eq_number_of_0, eq_0_number_of, less_0_number_of,
   of_int_number_of_eq, of_nat_number_of_eq, nat_number_of, if_True, if_False];

val simprocs = [Nat_Numeral_Simprocs.combine_numerals]@
                Nat_Numeral_Simprocs.cancel_numerals;

in

val nat_simprocs_setup =
 [Fast_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, simpset} =>
   {add_mono_thms = add_mono_thms, mult_mono_thms = mult_mono_thms,
    inj_thms = inj_thms, lessD = lessD,
    simpset = simpset addsimps add_rules
                      addsimprocs simprocs})];

end;
