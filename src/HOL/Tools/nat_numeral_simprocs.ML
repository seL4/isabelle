(* Author: Lawrence C Paulson, Cambridge University Computer Laboratory

Simprocs for nat numerals.
*)

signature NAT_NUMERAL_SIMPROCS =
sig
  val combine_numerals: simpset -> cterm -> thm option
  val eq_cancel_numerals: simpset -> cterm -> thm option
  val less_cancel_numerals: simpset -> cterm -> thm option
  val le_cancel_numerals: simpset -> cterm -> thm option
  val diff_cancel_numerals: simpset -> cterm -> thm option
  val eq_cancel_numeral_factor: simpset -> cterm -> thm option
  val less_cancel_numeral_factor: simpset -> cterm -> thm option
  val le_cancel_numeral_factor: simpset -> cterm -> thm option
  val div_cancel_numeral_factor: simpset -> cterm -> thm option
  val dvd_cancel_numeral_factor: simpset -> cterm -> thm option
  val eq_cancel_factor: simpset -> cterm -> thm option
  val less_cancel_factor: simpset -> cterm -> thm option
  val le_cancel_factor: simpset -> cterm -> thm option
  val div_cancel_factor: simpset -> cterm -> thm option
  val dvd_cancel_factor: simpset -> cterm -> thm option
end;

structure Nat_Numeral_Simprocs : NAT_NUMERAL_SIMPROCS =
struct

(*Maps n to #n for n = 1, 2*)
val numeral_syms = [@{thm numeral_1_eq_1} RS sym, @{thm numeral_2_eq_2} RS sym];
val numeral_sym_ss = HOL_basic_ss addsimps numeral_syms;

val rename_numerals = simplify numeral_sym_ss o Thm.transfer @{theory};

(*Utilities*)

fun mk_number 1 = HOLogic.numeral_const HOLogic.natT $ HOLogic.one_const
  | mk_number n = HOLogic.mk_number HOLogic.natT n;
fun dest_number t = Int.max (0, snd (HOLogic.dest_number t));

fun find_first_numeral past (t::terms) =
        ((dest_number t, t, rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_number 0;
val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = HOLogic.zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = HOLogic.dest_bin @{const_name Groups.plus} HOLogic.natT;


(** Other simproc items **)

val bin_simps =
     [@{thm numeral_1_eq_1} RS sym,
      @{thm numeral_plus_numeral}, @{thm add_numeral_left},
      @{thm diff_nat_numeral}, @{thm diff_0_eq_0}, @{thm diff_0},
      @{thm numeral_times_numeral}, @{thm mult_numeral_left(1)},
      @{thm if_True}, @{thm if_False}, @{thm not_False_eq_True},
      @{thm nat_0}, @{thm nat_numeral}, @{thm nat_neg_numeral}] @
     @{thms arith_simps} @ @{thms rel_simps};


(*** CancelNumerals simprocs ***)

val one = mk_number 1;
val mk_times = HOLogic.mk_binop @{const_name Groups.times};

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = HOLogic.dest_bin @{const_name Groups.times} HOLogic.natT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k,t) = mk_times (mk_number k, t);

(*Express t as a product of (possibly) a numeral with other factors, sorted*)
fun dest_coeff t =
    let val ts = sort Term_Ord.term_ord (dest_prod t)
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


(*Split up a sum into the list of its constituent terms, on the way removing any
  Sucs and counting them.*)
fun dest_Suc_sum (Const (@{const_name Suc}, _) $ t, (k,ts)) = dest_Suc_sum (t, (k+1,ts))
  | dest_Suc_sum (t, (k,ts)) = 
      let val (t1,t2) = dest_plus t
      in  dest_Suc_sum (t1, dest_Suc_sum (t2, (k,ts)))  end
      handle TERM _ => (k, t::ts);

(*Code for testing whether numerals are already used in the goal*)
fun is_numeral (Const(@{const_name Num.numeral}, _) $ w) = true
  | is_numeral _ = false;

fun prod_has_numeral t = exists is_numeral (dest_prod t);

(*The Sucs found in the term are converted to a binary numeral. If relaxed is false,
  an exception is raised unless the original expression contains at least one
  numeral in a coefficient position.  This prevents nat_combine_numerals from 
  introducing numerals to goals.*)
fun dest_Sucs_sum relaxed t = 
  let val (k,ts) = dest_Suc_sum (t,(0,[]))
  in
     if relaxed orelse exists prod_has_numeral ts then 
       if k=0 then ts
       else mk_number k :: ts
     else raise TERM("Nat_Numeral_Simprocs.dest_Sucs_sum", [t])
  end;


(*Simplify 1*n and n*1 to n*)
val add_0s  = map rename_numerals [@{thm Nat.add_0}, @{thm Nat.add_0_right}];
val mult_1s = map rename_numerals [@{thm nat_mult_1}, @{thm nat_mult_1_right}];

(*Final simplification: cancel + and *; replace Numeral0 by 0 and Numeral1 by 1*)

(*And these help the simproc return False when appropriate, which helps
  the arith prover.*)
val contra_rules = [@{thm add_Suc}, @{thm add_Suc_right}, @{thm Zero_not_Suc},
  @{thm Suc_not_Zero}, @{thm le_0_eq}];

val simplify_meta_eq =
    Arith_Data.simplify_meta_eq
        ([@{thm numeral_1_eq_Suc_0}, @{thm Nat.add_0}, @{thm Nat.add_0_right},
          @{thm mult_0}, @{thm mult_0_right}, @{thm mult_1}, @{thm mult_1_right}] @ contra_rules);


(*** Applying CancelNumeralsFun ***)

structure CancelNumeralsCommon =
struct
  val mk_sum = (fn T : typ => mk_sum)
  val dest_sum = dest_Sucs_sum true
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff
  val find_first_coeff = find_first_coeff []
  val trans_tac = Numeral_Simprocs.trans_tac

  val norm_ss1 = Numeral_Simprocs.num_ss addsimps numeral_syms @ add_0s @ mult_1s @
    [@{thm Suc_eq_plus1_left}] @ @{thms add_ac}
  val norm_ss2 = Numeral_Simprocs.num_ss addsimps bin_simps @ @{thms add_ac} @ @{thms mult_ac}
  fun norm_tac ss = 
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))

  val numeral_simp_ss = HOL_basic_ss addsimps add_0s @ bin_simps;
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss));
  val simplify_meta_eq  = simplify_meta_eq
  val prove_conv = Arith_Data.prove_conv
end;

structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} HOLogic.natT
  val bal_add1 = @{thm nat_eq_add_iff1} RS trans
  val bal_add2 = @{thm nat_eq_add_iff2} RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} HOLogic.natT
  val bal_add1 = @{thm nat_less_add_iff1} RS trans
  val bal_add2 = @{thm nat_less_add_iff2} RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} HOLogic.natT
  val bal_add1 = @{thm nat_le_add_iff1} RS trans
  val bal_add2 = @{thm nat_le_add_iff2} RS trans
);

structure DiffCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val mk_bal   = HOLogic.mk_binop @{const_name Groups.minus}
  val dest_bal = HOLogic.dest_bin @{const_name Groups.minus} HOLogic.natT
  val bal_add1 = @{thm nat_diff_add_eq1} RS trans
  val bal_add2 = @{thm nat_diff_add_eq2} RS trans
);

fun eq_cancel_numerals ss ct = EqCancelNumerals.proc ss (term_of ct)
fun less_cancel_numerals ss ct = LessCancelNumerals.proc ss (term_of ct)
fun le_cancel_numerals ss ct = LeCancelNumerals.proc ss (term_of ct)
fun diff_cancel_numerals ss ct = DiffCancelNumerals.proc ss (term_of ct)


(*** Applying CombineNumeralsFun ***)

structure CombineNumeralsData =
struct
  type coeff = int
  val iszero = (fn x => x = 0)
  val add = op +
  val mk_sum = (fn T : typ => long_mk_sum)  (*to work for 2*x + 3*x *)
  val dest_sum = dest_Sucs_sum false
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff
  val left_distrib = @{thm left_add_mult_distrib} RS trans
  val prove_conv = Arith_Data.prove_conv_nohyps
  val trans_tac = Numeral_Simprocs.trans_tac

  val norm_ss1 = Numeral_Simprocs.num_ss addsimps numeral_syms @ add_0s @ mult_1s @ [@{thm Suc_eq_plus1}] @ @{thms add_ac}
  val norm_ss2 = Numeral_Simprocs.num_ss addsimps bin_simps @ @{thms add_ac} @ @{thms mult_ac}
  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))

  val numeral_simp_ss = HOL_basic_ss addsimps add_0s @ bin_simps;
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = simplify_meta_eq
end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

fun combine_numerals ss ct = CombineNumerals.proc ss (term_of ct)


(*** Applying CancelNumeralFactorFun ***)

structure CancelNumeralFactorCommon =
struct
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff
  val trans_tac = Numeral_Simprocs.trans_tac

  val norm_ss1 = Numeral_Simprocs.num_ss addsimps
    numeral_syms @ add_0s @ mult_1s @ [@{thm Suc_eq_plus1_left}] @ @{thms add_ac}
  val norm_ss2 = Numeral_Simprocs.num_ss addsimps bin_simps @ @{thms add_ac} @ @{thms mult_ac}
  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))

  val numeral_simp_ss = HOL_basic_ss addsimps bin_simps
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = simplify_meta_eq
  val prove_conv = Arith_Data.prove_conv
end;

structure DivCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binop @{const_name Divides.div}
  val dest_bal = HOLogic.dest_bin @{const_name Divides.div} HOLogic.natT
  val cancel = @{thm nat_mult_div_cancel1} RS trans
  val neg_exchanges = false
);

structure DvdCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Rings.dvd}
  val dest_bal = HOLogic.dest_bin @{const_name Rings.dvd} HOLogic.natT
  val cancel = @{thm nat_mult_dvd_cancel1} RS trans
  val neg_exchanges = false
);

structure EqCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} HOLogic.natT
  val cancel = @{thm nat_mult_eq_cancel1} RS trans
  val neg_exchanges = false
);

structure LessCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} HOLogic.natT
  val cancel = @{thm nat_mult_less_cancel1} RS trans
  val neg_exchanges = true
);

structure LeCancelNumeralFactor = CancelNumeralFactorFun
 (open CancelNumeralFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} HOLogic.natT
  val cancel = @{thm nat_mult_le_cancel1} RS trans
  val neg_exchanges = true
)

fun eq_cancel_numeral_factor ss ct = EqCancelNumeralFactor.proc ss (term_of ct)
fun less_cancel_numeral_factor ss ct = LessCancelNumeralFactor.proc ss (term_of ct)
fun le_cancel_numeral_factor ss ct = LeCancelNumeralFactor.proc ss (term_of ct)
fun div_cancel_numeral_factor ss ct = DivCancelNumeralFactor.proc ss (term_of ct)
fun dvd_cancel_numeral_factor ss ct = DvdCancelNumeralFactor.proc ss (term_of ct)


(*** Applying ExtractCommonTermFun ***)

(*this version ALWAYS includes a trailing one*)
fun long_mk_prod []        = one
  | long_mk_prod (t :: ts) = mk_times (t, mk_prod ts);

(*Find first term that matches u*)
fun find_first_t past u []         = raise TERM("find_first_t", [])
  | find_first_t past u (t::terms) =
        if u aconv t then (rev past @ terms)
        else find_first_t (t::past) u terms
        handle TERM _ => find_first_t (t::past) u terms;

(** Final simplification for the CancelFactor simprocs **)
val simplify_one = Arith_Data.simplify_meta_eq  
  [@{thm mult_1_left}, @{thm mult_1_right}, @{thm div_1}, @{thm numeral_1_eq_Suc_0}];

fun cancel_simplify_meta_eq ss cancel_th th =
    simplify_one ss (([th, cancel_th]) MRS trans);

structure CancelFactorCommon =
struct
  val mk_sum = (fn T : typ => long_mk_prod)
  val dest_sum = dest_prod
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff
  val find_first = find_first_t []
  val trans_tac = Numeral_Simprocs.trans_tac
  val norm_ss = HOL_basic_ss addsimps mult_1s @ @{thms mult_ac}
  fun norm_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss))
  val simplify_meta_eq  = cancel_simplify_meta_eq
  fun mk_eq (a, b) = HOLogic.mk_Trueprop (HOLogic.mk_eq (a, b))
end;

structure EqCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} HOLogic.natT
  fun simp_conv _ _ = SOME @{thm nat_mult_eq_cancel_disj}
);

structure LeCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} HOLogic.natT
  fun simp_conv _ _ = SOME @{thm nat_mult_le_cancel_disj}
);

structure LessCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} HOLogic.natT
  fun simp_conv _ _ = SOME @{thm nat_mult_less_cancel_disj}
);

structure DivideCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binop @{const_name Divides.div}
  val dest_bal = HOLogic.dest_bin @{const_name Divides.div} HOLogic.natT
  fun simp_conv _ _ = SOME @{thm nat_mult_div_cancel_disj}
);

structure DvdCancelFactor = ExtractCommonTermFun
 (open CancelFactorCommon
  val mk_bal   = HOLogic.mk_binrel @{const_name Rings.dvd}
  val dest_bal = HOLogic.dest_bin @{const_name Rings.dvd} HOLogic.natT
  fun simp_conv _ _ = SOME @{thm nat_mult_dvd_cancel_disj}
);

fun eq_cancel_factor ss ct = EqCancelFactor.proc ss (term_of ct)
fun less_cancel_factor ss ct = LessCancelFactor.proc ss (term_of ct)
fun le_cancel_factor ss ct = LeCancelFactor.proc ss (term_of ct)
fun div_cancel_factor ss ct = DivideCancelFactor.proc ss (term_of ct)
fun dvd_cancel_factor ss ct = DvdCancelFactor.proc ss (term_of ct)

end;
