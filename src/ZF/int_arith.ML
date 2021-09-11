(*  Title:      ZF/int_arith.ML
    Author:     Larry Paulson

Simprocs for linear arithmetic.
*)

signature INT_NUMERAL_SIMPROCS =
sig
  val cancel_numerals: simproc list
  val combine_numerals: simproc
  val combine_numerals_prod: simproc
end

structure Int_Numeral_Simprocs: INT_NUMERAL_SIMPROCS =
struct

(* abstract syntax operations *)

fun mk_bit 0 = \<^term>\<open>0\<close>
  | mk_bit 1 = \<^term>\<open>succ(0)\<close>
  | mk_bit _ = raise TERM ("mk_bit", []);

fun dest_bit \<^term>\<open>0\<close> = 0
  | dest_bit \<^term>\<open>succ(0)\<close> = 1
  | dest_bit t = raise TERM ("dest_bit", [t]);

fun mk_bin i =
  let
    fun term_of [] = \<^term>\<open>Pls\<close>
      | term_of [~1] = \<^term>\<open>Min\<close>
      | term_of (b :: bs) = \<^term>\<open>Bit\<close> $ term_of bs $ mk_bit b;
  in term_of (Numeral_Syntax.make_binary i) end;

fun dest_bin tm =
  let
    fun bin_of \<^term>\<open>Pls\<close> = []
      | bin_of \<^term>\<open>Min\<close> = [~1]
      | bin_of (\<^term>\<open>Bit\<close> $ bs $ b) = dest_bit b :: bin_of bs
      | bin_of _ = raise TERM ("dest_bin", [tm]);
  in Numeral_Syntax.dest_binary (bin_of tm) end;


(*Utilities*)

fun mk_numeral i = \<^const>\<open>integ_of\<close> $ mk_bin i;

fun dest_numeral \<^Const_>\<open>integ_of for w\<close> = dest_bin w
  | dest_numeral t = raise TERM ("dest_numeral", [t]);

fun find_first_numeral past (t::terms) =
        ((dest_numeral t, rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = FOLogic.mk_binop \<^const_name>\<open>zadd\<close>;

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, \<^Const_>\<open>zadd for t u\<close>, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, \<^Const_>\<open>zdiff for t u\<close>, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else \<^const>\<open>zminus\<close> $ t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val one = mk_numeral 1;
val mk_times = FOLogic.mk_binop \<^const_name>\<open>zmult\<close>;

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = FOLogic.dest_bin \<^const_name>\<open>zmult\<close> \<^typ>\<open>i\<close>;

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, t) = mk_times (mk_numeral k, t);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign \<^Const_>\<open>zminus for t\<close> = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort Term_Ord.term_ord (dest_prod t)
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


(*Simplify #1*n and n*#1 to n*)
val add_0s = [@{thm zadd_0_intify}, @{thm zadd_0_right_intify}];

val mult_1s = [@{thm zmult_1_intify}, @{thm zmult_1_right_intify},
               @{thm zmult_minus1}, @{thm zmult_minus1_right}];

val tc_rules = [@{thm integ_of_type}, @{thm intify_in_int},
                @{thm int_of_type}, @{thm zadd_type}, @{thm zdiff_type}, @{thm zmult_type}] @ 
               @{thms bin.intros};
val intifys = [@{thm intify_ident}, @{thm zadd_intify1}, @{thm zadd_intify2},
               @{thm zdiff_intify1}, @{thm zdiff_intify2}, @{thm zmult_intify1}, @{thm zmult_intify2},
               @{thm zless_intify1}, @{thm zless_intify2}, @{thm zle_intify1}, @{thm zle_intify2}];

(*To perform binary arithmetic*)
val bin_simps = [@{thm add_integ_of_left}] @ @{thms bin_arith_simps} @ @{thms bin_rel_simps};

(*To evaluate binary negations of coefficients*)
val zminus_simps = @{thms NCons_simps} @
                   [@{thm integ_of_minus} RS @{thm sym},
                    @{thm bin_minus_1}, @{thm bin_minus_0}, @{thm bin_minus_Pls}, @{thm bin_minus_Min},
                    @{thm bin_pred_1}, @{thm bin_pred_0}, @{thm bin_pred_Pls}, @{thm bin_pred_Min}];

(*To let us treat subtraction as addition*)
val diff_simps = [@{thm zdiff_def}, @{thm zminus_zadd_distrib}, @{thm zminus_zminus}];

(*push the unary minus down*)
val int_minus_mult_eq_1_to_2 = @{lemma "$- w $* z = w $* $- z" by simp};

(*to extract again any uncancelled minuses*)
val int_minus_from_mult_simps =
    [@{thm zminus_zminus}, @{thm zmult_zminus}, @{thm zmult_zminus_right}];

(*combine unary minus with numeric literals, however nested within a product*)
val int_mult_minus_simps =
    [@{thm zmult_assoc}, @{thm zmult_zminus} RS @{thm sym}, int_minus_mult_eq_1_to_2];

structure CancelNumeralsCommon =
  struct
  val mk_sum = (fn _ : typ => mk_sum)
  val dest_sum = dest_sum
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff 1
  val find_first_coeff = find_first_coeff []
  fun trans_tac ctxt = ArithData.gen_trans_tac ctxt @{thm iff_trans}

  val norm_ss1 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps add_0s @ mult_1s @ diff_simps @ zminus_simps @ @{thms zadd_ac})
  val norm_ss2 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps bin_simps @ int_mult_minus_simps @ intifys)
  val norm_ss3 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps int_minus_from_mult_simps @ @{thms zadd_ac} @ @{thms zmult_ac} @ tc_rules @ intifys)
  fun norm_tac ctxt =
    ALLGOALS (asm_simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (asm_simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (asm_simp_tac (put_simpset norm_ss3 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps add_0s @ bin_simps @ tc_rules @ intifys)
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
    THEN ALLGOALS (asm_simp_tac ctxt)
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s @ mult_1s)
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "inteq_cancel_numerals"
  val mk_bal   = FOLogic.mk_eq
  val dest_bal = FOLogic.dest_eq
  val bal_add1 = @{thm eq_add_iff1} RS @{thm iff_trans}
  val bal_add2 = @{thm eq_add_iff2} RS @{thm iff_trans}
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intless_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel \<^const_name>\<open>zless\<close>
  val dest_bal = FOLogic.dest_bin \<^const_name>\<open>zless\<close> \<^typ>\<open>i\<close>
  val bal_add1 = @{thm less_add_iff1} RS @{thm iff_trans}
  val bal_add2 = @{thm less_add_iff2} RS @{thm iff_trans}
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intle_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel \<^const_name>\<open>zle\<close>
  val dest_bal = FOLogic.dest_bin \<^const_name>\<open>zle\<close> \<^typ>\<open>i\<close>
  val bal_add1 = @{thm le_add_iff1} RS @{thm iff_trans}
  val bal_add2 = @{thm le_add_iff2} RS @{thm iff_trans}
);

val cancel_numerals =
 [Simplifier.make_simproc \<^context> "inteq_cancel_numerals"
   {lhss =
     [\<^term>\<open>l $+ m = n\<close>, \<^term>\<open>l = m $+ n\<close>,
      \<^term>\<open>l $- m = n\<close>, \<^term>\<open>l = m $- n\<close>,
      \<^term>\<open>l $* m = n\<close>, \<^term>\<open>l = m $* n\<close>],
    proc = K EqCancelNumerals.proc},
  Simplifier.make_simproc \<^context> "intless_cancel_numerals"
   {lhss =
     [\<^term>\<open>l $+ m $< n\<close>, \<^term>\<open>l $< m $+ n\<close>,
      \<^term>\<open>l $- m $< n\<close>, \<^term>\<open>l $< m $- n\<close>,
      \<^term>\<open>l $* m $< n\<close>, \<^term>\<open>l $< m $* n\<close>],
    proc = K LessCancelNumerals.proc},
  Simplifier.make_simproc \<^context> "intle_cancel_numerals"
   {lhss =
     [\<^term>\<open>l $+ m $\<le> n\<close>, \<^term>\<open>l $\<le> m $+ n\<close>,
      \<^term>\<open>l $- m $\<le> n\<close>, \<^term>\<open>l $\<le> m $- n\<close>,
      \<^term>\<open>l $* m $\<le> n\<close>, \<^term>\<open>l $\<le> m $* n\<close>],
    proc = K LeCancelNumerals.proc}];


(*version without the hyps argument*)
fun prove_conv_nohyps name tacs sg = ArithData.prove_conv name tacs sg [];

structure CombineNumeralsData =
  struct
  type coeff = int
  val iszero = (fn x => x = 0)
  val add = op + 
  val mk_sum = (fn _ : typ => long_mk_sum) (*to work for #2*x $+ #3*x *)
  val dest_sum = dest_sum
  val mk_coeff = mk_coeff
  val dest_coeff = dest_coeff 1
  val left_distrib = @{thm left_zadd_zmult_distrib} RS @{thm trans}
  val prove_conv = prove_conv_nohyps "int_combine_numerals"
  fun trans_tac ctxt = ArithData.gen_trans_tac ctxt @{thm trans}

  val norm_ss1 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps add_0s @ mult_1s @ diff_simps @ zminus_simps @ @{thms zadd_ac} @ intifys)
  val norm_ss2 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps bin_simps @ int_mult_minus_simps @ intifys)
  val norm_ss3 =
    simpset_of (put_simpset ZF_ss \<^context>
      addsimps int_minus_from_mult_simps @ @{thms zadd_ac} @ @{thms zmult_ac} @ tc_rules @ intifys)
  fun norm_tac ctxt =
    ALLGOALS (asm_simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (asm_simp_tac (put_simpset norm_ss2 ctxt))
    THEN ALLGOALS (asm_simp_tac (put_simpset norm_ss3 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset ZF_ss \<^context> addsimps add_0s @ bin_simps @ tc_rules @ intifys)
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s @ mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  Simplifier.make_simproc \<^context> "int_combine_numerals"
    {lhss = [\<^term>\<open>i $+ j\<close>, \<^term>\<open>i $- j\<close>],
     proc = K CombineNumerals.proc};



(** Constant folding for integer multiplication **)

(*The trick is to regard products as sums, e.g. #3 $* x $* #4 as
  the "sum" of #3, x, #4; the literals are then multiplied*)


structure CombineNumeralsProdData =
struct
  type coeff = int
  val iszero = (fn x => x = 0)
  val add = op *
  val mk_sum = (fn _ : typ => mk_prod)
  val dest_sum = dest_prod
  fun mk_coeff(k,t) =
    if t = one then mk_numeral k
    else raise TERM("mk_coeff", [])
  fun dest_coeff t = (dest_numeral t, one)  (*We ONLY want pure numerals.*)
  val left_distrib = @{thm zmult_assoc} RS @{thm sym} RS @{thm trans}
  val prove_conv = prove_conv_nohyps "int_combine_numerals_prod"
  fun trans_tac ctxt = ArithData.gen_trans_tac ctxt @{thm trans}

  val norm_ss1 =
    simpset_of (put_simpset ZF_ss \<^context> addsimps mult_1s @ diff_simps @ zminus_simps)
  val norm_ss2 =
    simpset_of (put_simpset ZF_ss \<^context> addsimps [@{thm zmult_zminus_right} RS @{thm sym}] @
    bin_simps @ @{thms zmult_ac} @ tc_rules @ intifys)
  fun norm_tac ctxt =
    ALLGOALS (asm_simp_tac (put_simpset norm_ss1 ctxt))
    THEN ALLGOALS (asm_simp_tac (put_simpset norm_ss2 ctxt))

  val numeral_simp_ss =
    simpset_of (put_simpset ZF_ss \<^context> addsimps bin_simps @ tc_rules @ intifys)
  fun numeral_simp_tac ctxt =
    ALLGOALS (simp_tac (put_simpset numeral_simp_ss ctxt))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (mult_1s);
end;


structure CombineNumeralsProd = CombineNumeralsFun(CombineNumeralsProdData);

val combine_numerals_prod =
  Simplifier.make_simproc \<^context> "int_combine_numerals_prod"
   {lhss = [\<^term>\<open>i $* j\<close>], proc = K CombineNumeralsProd.proc};

end;

val _ =
  Theory.setup (Simplifier.map_theory_simpset (fn ctxt =>
    ctxt addsimprocs
      (Int_Numeral_Simprocs.cancel_numerals @
       [Int_Numeral_Simprocs.combine_numerals,
        Int_Numeral_Simprocs.combine_numerals_prod])));
