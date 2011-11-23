(*  Title:      ZF/arith_data.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Arithmetic simplification: cancellation of common terms
*)

signature ARITH_DATA =
sig
  (*the main outcome*)
  val nat_cancel: simproc list
  (*tools for use in similar applications*)
  val gen_trans_tac: thm -> thm option -> tactic
  val prove_conv: string -> tactic list -> Proof.context -> thm list -> term * term -> thm option
  val simplify_meta_eq: thm list -> simpset -> thm -> thm
  (*debugging*)
  structure EqCancelNumeralsData   : CANCEL_NUMERALS_DATA
  structure LessCancelNumeralsData : CANCEL_NUMERALS_DATA
  structure DiffCancelNumeralsData : CANCEL_NUMERALS_DATA
end;


structure ArithData: ARITH_DATA =
struct

val iT = Ind_Syntax.iT;

val zero = Const(@{const_name zero}, iT);
val succ = Const(@{const_name succ}, iT --> iT);
fun mk_succ t = succ $ t;
val one = mk_succ zero;

val mk_plus = FOLogic.mk_binop @{const_name Arith.add};

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = FOLogic.dest_bin @{const_name Arith.add} iT;

(* dest_sum *)

fun dest_sum (Const(@{const_name zero},_)) = []
  | dest_sum (Const(@{const_name succ},_) $ t) = one :: dest_sum t
  | dest_sum (Const(@{const_name Arith.add},_) $ t $ u) = dest_sum t @ dest_sum u
  | dest_sum tm = [tm];

(*Apply the given rewrite (if present) just once*)
fun gen_trans_tac th2 NONE      = all_tac
  | gen_trans_tac th2 (SOME th) = ALLGOALS (rtac (th RS th2));

(*Use <-> or = depending on the type of t*)
fun mk_eq_iff(t,u) =
  if fastype_of t = iT then FOLogic.mk_eq(t,u)
                       else FOLogic.mk_iff(t,u);

(*We remove equality assumptions because they confuse the simplifier and
  because only type-checking assumptions are necessary.*)
fun is_eq_thm th =
    can FOLogic.dest_eq (FOLogic.dest_Trueprop (Thm.prop_of th));

fun add_chyps chyps ct = Drule.list_implies (map cprop_of chyps, ct);

fun prove_conv name tacs ctxt prems (t,u) =
  if t aconv u then NONE
  else
  let val prems' = filter_out is_eq_thm prems
      val goal = Logic.list_implies (map Thm.prop_of prems',
        FOLogic.mk_Trueprop (mk_eq_iff (t, u)));
  in SOME (prems' MRS Goal.prove ctxt [] [] goal (K (EVERY tacs)))
      handle ERROR msg =>
        (warning (msg ^ "\nCancellation failed: no typing information? (" ^ name ^ ")"); NONE)
  end;

fun prep_simproc thy (name, pats, proc) =
  Simplifier.simproc_global thy name pats proc;


(*** Use CancelNumerals simproc without binary numerals,
     just for cancellation ***)

val mk_times = FOLogic.mk_binop @{const_name Arith.mult};

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = FOLogic.dest_bin @{const_name Arith.mult} iT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*Dummy version: the only arguments are 0 and 1*)
fun mk_coeff (0, t) = zero
  | mk_coeff (1, t) = t
  | mk_coeff _       = raise TERM("mk_coeff", []);

(*Dummy version: the "coefficient" is always 1.
  In the result, the factors are sorted terms*)
fun dest_coeff t = (1, mk_prod (sort Term_Ord.term_ord (dest_prod t)));

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff t
        in  if u aconv u' then (n, rev past @ terms)
                          else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms;


(*Simplify #1*n and n*#1 to n*)
val add_0s = [@{thm add_0_natify}, @{thm add_0_right_natify}];
val add_succs = [@{thm add_succ}, @{thm add_succ_right}];
val mult_1s = [@{thm mult_1_natify}, @{thm mult_1_right_natify}];
val tc_rules = [@{thm natify_in_nat}, @{thm add_type}, @{thm diff_type}, @{thm mult_type}];
val natifys = [@{thm natify_0}, @{thm natify_ident}, @{thm add_natify1}, @{thm add_natify2},
               @{thm diff_natify1}, @{thm diff_natify2}];

(*Final simplification: cancel + and **)
fun simplify_meta_eq rules =
  let val ss0 =
    FOL_ss
      delsimps @{thms iff_simps} (*these could erase the whole rule!*)
      addsimps rules
      |> fold Simplifier.add_eqcong [@{thm eq_cong2}, @{thm iff_cong2}]
  in fn ss => mk_meta_eq o simplify (Simplifier.inherit_context ss ss0) end;

val final_rules = add_0s @ mult_1s @ [@{thm mult_0}, @{thm mult_0_right}];

structure CancelNumeralsCommon =
  struct
  val mk_sum            = (fn T:typ => mk_sum)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff
  val find_first_coeff  = find_first_coeff []

  val norm_ss1 = ZF_ss addsimps add_0s @ add_succs @ mult_1s @ @{thms add_ac}
  val norm_ss2 = ZF_ss addsimps add_0s @ mult_1s @ @{thms add_ac} @
    @{thms mult_ac} @ tc_rules @ natifys
  fun norm_tac ss =
    ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss norm_ss2))
  val numeral_simp_ss = ZF_ss addsimps add_0s @ tc_rules @ natifys
  fun numeral_simp_tac ss =
    ALLGOALS (asm_simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq  = simplify_meta_eq final_rules
  end;

(** The functor argumnets are declared as separate structures
    so that they can be exported to ease debugging. **)

structure EqCancelNumeralsData =
  struct
  open CancelNumeralsCommon
  val prove_conv = prove_conv "nateq_cancel_numerals"
  val mk_bal   = FOLogic.mk_eq
  val dest_bal = FOLogic.dest_eq
  val bal_add1 = @{thm eq_add_iff} RS @{thm iff_trans}
  val bal_add2 = @{thm eq_add_iff} RS @{thm iff_trans}
  val trans_tac = gen_trans_tac @{thm iff_trans}
  end;

structure EqCancelNumerals = CancelNumeralsFun(EqCancelNumeralsData);

structure LessCancelNumeralsData =
  struct
  open CancelNumeralsCommon
  val prove_conv = prove_conv "natless_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel @{const_name Ordinal.lt}
  val dest_bal = FOLogic.dest_bin @{const_name Ordinal.lt} iT
  val bal_add1 = @{thm less_add_iff} RS @{thm iff_trans}
  val bal_add2 = @{thm less_add_iff} RS @{thm iff_trans}
  val trans_tac = gen_trans_tac @{thm iff_trans}
  end;

structure LessCancelNumerals = CancelNumeralsFun(LessCancelNumeralsData);

structure DiffCancelNumeralsData =
  struct
  open CancelNumeralsCommon
  val prove_conv = prove_conv "natdiff_cancel_numerals"
  val mk_bal   = FOLogic.mk_binop @{const_name Arith.diff}
  val dest_bal = FOLogic.dest_bin @{const_name Arith.diff} iT
  val bal_add1 = @{thm diff_add_eq} RS @{thm trans}
  val bal_add2 = @{thm diff_add_eq} RS @{thm trans}
  val trans_tac = gen_trans_tac @{thm trans}
  end;

structure DiffCancelNumerals = CancelNumeralsFun(DiffCancelNumeralsData);


val nat_cancel =
  map (prep_simproc @{theory})
   [("nateq_cancel_numerals",
     ["l #+ m = n", "l = m #+ n",
      "l #* m = n", "l = m #* n",
      "succ(m) = n", "m = succ(n)"],
     (K EqCancelNumerals.proc)),
    ("natless_cancel_numerals",
     ["l #+ m < n", "l < m #+ n",
      "l #* m < n", "l < m #* n",
      "succ(m) < n", "m < succ(n)"],
     (K LessCancelNumerals.proc)),
    ("natdiff_cancel_numerals",
     ["(l #+ m) #- n", "l #- (m #+ n)",
      "(l #* m) #- n", "l #- (m #* n)",
      "succ(m) #- n", "m #- succ(n)"],
     (K DiffCancelNumerals.proc))];

end;

Addsimprocs ArithData.nat_cancel;


(*examples:
print_depth 22;
set timing;
set simp_trace;
fun test s = (Goal s; by (Asm_simp_tac 1));

test "x #+ y = x #+ z";
test "y #+ x = x #+ z";
test "x #+ y #+ z = x #+ z";
test "y #+ (z #+ x) = z #+ x";
test "x #+ y #+ z = (z #+ y) #+ (x #+ w)";
test "x#*y #+ z = (z #+ y) #+ (y#*x #+ w)";

test "x #+ succ(y) = x #+ z";
test "x #+ succ(y) = succ(z #+ x)";
test "succ(x) #+ succ(y) #+ z = succ(z #+ y) #+ succ(x #+ w)";

test "(x #+ y) #- (x #+ z) = w";
test "(y #+ x) #- (x #+ z) = dd";
test "(x #+ y #+ z) #- (x #+ z) = dd";
test "(y #+ (z #+ x)) #- (z #+ x) = dd";
test "(x #+ y #+ z) #- ((z #+ y) #+ (x #+ w)) = dd";
test "(x#*y #+ z) #- ((z #+ y) #+ (y#*x #+ w)) = dd";

(*BAD occurrence of natify*)
test "(x #+ succ(y)) #- (x #+ z) = dd";

test "x #* y2 #+ y #* x2 = y #* x2 #+ x #* y2";

test "(x #+ succ(y)) #- (succ(z #+ x)) = dd";
test "(succ(x) #+ succ(y) #+ z) #- (succ(z #+ y) #+ succ(x #+ w)) = dd";

(*use of typing information*)
test "x : nat ==> x #+ y = x";
test "x : nat --> x #+ y = x";
test "x : nat ==> x #+ y < x";
test "x : nat ==> x < y#+x";
test "x : nat ==> x le succ(x)";

(*fails: no typing information isn't visible*)
test "x #+ y = x";

test "x #+ y < x #+ z";
test "y #+ x < x #+ z";
test "x #+ y #+ z < x #+ z";
test "y #+ z #+ x < x #+ z";
test "y #+ (z #+ x) < z #+ x";
test "x #+ y #+ z < (z #+ y) #+ (x #+ w)";
test "x#*y #+ z < (z #+ y) #+ (y#*x #+ w)";

test "x #+ succ(y) < x #+ z";
test "x #+ succ(y) < succ(z #+ x)";
test "succ(x) #+ succ(y) #+ z < succ(z #+ y) #+ succ(x #+ w)";

test "x #+ succ(y) le succ(z #+ x)";
*)
