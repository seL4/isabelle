(*  Title:      ZF/int_arith.ML
    Author:     Larry Paulson

Simprocs for linear arithmetic.
*)

structure Int_Numeral_Simprocs =
struct

(*Utilities*)

fun mk_numeral n = @{const integ_of} $ NumeralSyntax.mk_bin n;

(*Decodes a binary INTEGER*)
fun dest_numeral (Const(@{const_name integ_of}, _) $ w) =
     (NumeralSyntax.dest_bin w
      handle Match => raise TERM("Int_Numeral_Simprocs.dest_numeral:1", [w]))
  | dest_numeral t =  raise TERM("Int_Numeral_Simprocs.dest_numeral:2", [t]);

fun find_first_numeral past (t::terms) =
        ((dest_numeral t, rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = FOLogic.mk_binop @{const_name "zadd"};

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = FOLogic.dest_bin @{const_name "zadd"} @{typ i};

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const (@{const_name "zadd"}, _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const (@{const_name "zdiff"}, _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else @{const zminus} $ t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = FOLogic.mk_binop @{const_name "zdiff"};
val dest_diff = FOLogic.dest_bin @{const_name "zdiff"} @{typ i};

val one = mk_numeral 1;
val mk_times = FOLogic.mk_binop @{const_name "zmult"};

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = FOLogic.dest_bin @{const_name "zmult"} @{typ i};

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, t) = mk_times (mk_numeral k, t);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const (@{const_name "zminus"}, _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort TermOrd.term_ord (dest_prod t)
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
                   [@{thm integ_of_minus} RS sym,
                    @{thm bin_minus_1}, @{thm bin_minus_0}, @{thm bin_minus_Pls}, @{thm bin_minus_Min},
                    @{thm bin_pred_1}, @{thm bin_pred_0}, @{thm bin_pred_Pls}, @{thm bin_pred_Min}];

(*To let us treat subtraction as addition*)
val diff_simps = [@{thm zdiff_def}, @{thm zminus_zadd_distrib}, @{thm zminus_zminus}];

(*push the unary minus down: - x * y = x * - y *)
val int_minus_mult_eq_1_to_2 =
    [@{thm zmult_zminus}, @{thm zmult_zminus_right} RS sym] MRS trans |> standard;

(*to extract again any uncancelled minuses*)
val int_minus_from_mult_simps =
    [@{thm zminus_zminus}, @{thm zmult_zminus}, @{thm zmult_zminus_right}];

(*combine unary minus with numeric literals, however nested within a product*)
val int_mult_minus_simps =
    [@{thm zmult_assoc}, @{thm zmult_zminus} RS sym, int_minus_mult_eq_1_to_2];

fun prep_simproc (name, pats, proc) =
  Simplifier.simproc (the_context ()) name pats proc;

structure CancelNumeralsCommon =
  struct
  val mk_sum            = (fn T:typ => mk_sum)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  fun trans_tac _       = ArithData.gen_trans_tac iff_trans

  val norm_ss1 = ZF_ss addsimps add_0s @ mult_1s @ diff_simps @ zminus_simps @ @{thms zadd_ac}
  val norm_ss2 = ZF_ss addsimps bin_simps @ int_mult_minus_simps @ intifys
  val norm_ss3 = ZF_ss addsimps int_minus_from_mult_simps @ @{thms zadd_ac} @ @{thms zmult_ac} @ tc_rules @ intifys
  fun norm_tac ss =
    ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = ZF_ss addsimps add_0s @ bin_simps @ tc_rules @ intifys
  fun numeral_simp_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
    THEN ALLGOALS (asm_simp_tac (simpset_of (Simplifier.the_context ss)))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s @ mult_1s)
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "inteq_cancel_numerals"
  val mk_bal   = FOLogic.mk_eq
  val dest_bal = FOLogic.dest_eq
  val bal_add1 = @{thm eq_add_iff1} RS iff_trans
  val bal_add2 = @{thm eq_add_iff2} RS iff_trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intless_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel @{const_name "zless"}
  val dest_bal = FOLogic.dest_bin @{const_name "zless"} @{typ i}
  val bal_add1 = @{thm less_add_iff1} RS iff_trans
  val bal_add2 = @{thm less_add_iff2} RS iff_trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intle_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel @{const_name "zle"}
  val dest_bal = FOLogic.dest_bin @{const_name "zle"} @{typ i}
  val bal_add1 = @{thm le_add_iff1} RS iff_trans
  val bal_add2 = @{thm le_add_iff2} RS iff_trans
);

val cancel_numerals =
  map prep_simproc
   [("inteq_cancel_numerals",
     ["l $+ m = n", "l = m $+ n",
      "l $- m = n", "l = m $- n",
      "l $* m = n", "l = m $* n"],
     K EqCancelNumerals.proc),
    ("intless_cancel_numerals",
     ["l $+ m $< n", "l $< m $+ n",
      "l $- m $< n", "l $< m $- n",
      "l $* m $< n", "l $< m $* n"],
     K LessCancelNumerals.proc),
    ("intle_cancel_numerals",
     ["l $+ m $<= n", "l $<= m $+ n",
      "l $- m $<= n", "l $<= m $- n",
      "l $* m $<= n", "l $<= m $* n"],
     K LeCancelNumerals.proc)];


(*version without the hyps argument*)
fun prove_conv_nohyps name tacs sg = ArithData.prove_conv name tacs sg [];

structure CombineNumeralsData =
  struct
  type coeff            = int
  val iszero            = (fn x => x = 0)
  val add               = op + 
  val mk_sum            = (fn T:typ => long_mk_sum) (*to work for #2*x $+ #3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = @{thm left_zadd_zmult_distrib} RS trans
  val prove_conv        = prove_conv_nohyps "int_combine_numerals"
  fun trans_tac _       = ArithData.gen_trans_tac trans

  val norm_ss1 = ZF_ss addsimps add_0s @ mult_1s @ diff_simps @ zminus_simps @ @{thms zadd_ac} @ intifys
  val norm_ss2 = ZF_ss addsimps bin_simps @ int_mult_minus_simps @ intifys
  val norm_ss3 = ZF_ss addsimps int_minus_from_mult_simps @ @{thms zadd_ac} @ @{thms zmult_ac} @ tc_rules @ intifys
  fun norm_tac ss =
    ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = ZF_ss addsimps add_0s @ bin_simps @ tc_rules @ intifys
  fun numeral_simp_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s @ mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

val combine_numerals =
  prep_simproc ("int_combine_numerals", ["i $+ j", "i $- j"], K CombineNumerals.proc);



(** Constant folding for integer multiplication **)

(*The trick is to regard products as sums, e.g. #3 $* x $* #4 as
  the "sum" of #3, x, #4; the literals are then multiplied*)


structure CombineNumeralsProdData =
  struct
  type coeff            = int
  val iszero            = (fn x => x = 0)
  val add               = op *
  val mk_sum            = (fn T:typ => mk_prod)
  val dest_sum          = dest_prod
  fun mk_coeff(k,t) = if t=one then mk_numeral k
                      else raise TERM("mk_coeff", [])
  fun dest_coeff t = (dest_numeral t, one)  (*We ONLY want pure numerals.*)
  val left_distrib      = @{thm zmult_assoc} RS sym RS trans
  val prove_conv        = prove_conv_nohyps "int_combine_numerals_prod"
  fun trans_tac _       = ArithData.gen_trans_tac trans



val norm_ss1 = ZF_ss addsimps mult_1s @ diff_simps @ zminus_simps
  val norm_ss2 = ZF_ss addsimps [@{thm zmult_zminus_right} RS sym] @
    bin_simps @ @{thms zmult_ac} @ tc_rules @ intifys
  fun norm_tac ss =
    ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss2))

  val numeral_simp_ss = ZF_ss addsimps bin_simps @ tc_rules @ intifys
  fun numeral_simp_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (mult_1s);
  end;


structure CombineNumeralsProd = CombineNumeralsFun(CombineNumeralsProdData);

val combine_numerals_prod =
  prep_simproc ("int_combine_numerals_prod", ["i $* j"], K CombineNumeralsProd.proc);

end;


Addsimprocs Int_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Int_Numeral_Simprocs.combine_numerals,
             Int_Numeral_Simprocs.combine_numerals_prod];


(*examples:*)
(*
print_depth 22;
set timing;
set trace_simp;
fun test s = (Goal s; by (Asm_simp_tac 1));
val sg = #sign (rep_thm (topthm()));
val t = FOLogic.dest_Trueprop (Logic.strip_assums_concl(getgoal 1));
val (t,_) = FOLogic.dest_eq t;

(*combine_numerals_prod (products of separate literals) *)
test "#5 $* x $* #3 = y";

test "y2 $+ ?x42 = y $+ y2";

test "oo : int ==> l $+ (l $+ #2) $+ oo = oo";

test "#9$*x $+ y = x$*#23 $+ z";
test "y $+ x = x $+ z";

test "x : int ==> x $+ y $+ z = x $+ z";
test "x : int ==> y $+ (z $+ x) = z $+ x";
test "z : int ==> x $+ y $+ z = (z $+ y) $+ (x $+ w)";
test "z : int ==> x$*y $+ z = (z $+ y) $+ (y$*x $+ w)";

test "#-3 $* x $+ y $<= x $* #2 $+ z";
test "y $+ x $<= x $+ z";
test "x $+ y $+ z $<= x $+ z";

test "y $+ (z $+ x) $< z $+ x";
test "x $+ y $+ z $< (z $+ y) $+ (x $+ w)";
test "x$*y $+ z $< (z $+ y) $+ (y$*x $+ w)";

test "l $+ #2 $+ #2 $+ #2 $+ (l $+ #2) $+ (oo $+ #2) = uu";
test "u : int ==> #2 $* u = u";
test "(i $+ j $+ #12 $+ k) $- #15 = y";
test "(i $+ j $+ #12 $+ k) $- #5 = y";

test "y $- b $< b";
test "y $- (#3 $* b $+ c) $< b $- #2 $* c";

test "(#2 $* x $- (u $* v) $+ y) $- v $* #3 $* u = w";
test "(#2 $* x $* u $* v $+ (u $* v) $* #4 $+ y) $- v $* u $* #4 = w";
test "(#2 $* x $* u $* v $+ (u $* v) $* #4 $+ y) $- v $* u = w";
test "u $* v $- (x $* u $* v $+ (u $* v) $* #4 $+ y) = w";

test "(i $+ j $+ #12 $+ k) = u $+ #15 $+ y";
test "(i $+ j $* #2 $+ #12 $+ k) = j $+ #5 $+ y";

test "#2 $* y $+ #3 $* z $+ #6 $* w $+ #2 $* y $+ #3 $* z $+ #2 $* u = #2 $* y' $+ #3 $* z' $+ #6 $* w' $+ #2 $* y' $+ #3 $* z' $+ u $+ vv";

test "a $+ $-(b$+c) $+ b = d";
test "a $+ $-(b$+c) $- b = d";

(*negative numerals*)
test "(i $+ j $+ #-2 $+ k) $- (u $+ #5 $+ y) = zz";
test "(i $+ j $+ #-3 $+ k) $< u $+ #5 $+ y";
test "(i $+ j $+ #3 $+ k) $< u $+ #-6 $+ y";
test "(i $+ j $+ #-12 $+ k) $- #15 = y";
test "(i $+ j $+ #12 $+ k) $- #-15 = y";
test "(i $+ j $+ #-12 $+ k) $- #-15 = y";

(*Multiplying separated numerals*)
Goal "#6 $* ($# x $* #2) =  uu";
Goal "#4 $* ($# x $* $# x) $* (#2 $* $# x) =  uu";
*)

