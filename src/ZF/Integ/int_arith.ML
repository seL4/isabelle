(*  Title:      ZF/Integ/int_arith.ML
    ID:         $Id$
    Author:    Larry Paulson
    Copyright   2000  University of Cambridge

Simprocs for linear arithmetic.
*)


(** To simplify inequalities involving integer negation and literals,
    such as -x = #3
**)

Addsimps [inst "y" "integ_of(?w)" zminus_equation,
          inst "x" "integ_of(?w)" equation_zminus];

AddIffs [inst "y" "integ_of(?w)" zminus_zless,
         inst "x" "integ_of(?w)" zless_zminus];

AddIffs [inst "y" "integ_of(?w)" zminus_zle,
         inst "x" "integ_of(?w)" zle_zminus];

Addsimps [inst "s" "integ_of(?w)" Let_def];

(*** Simprocs for numeric literals ***)

(** Combining of literal coefficients in sums of products **)

Goal "(x $< y) <-> (x$-y $< #0)";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zless_iff_zdiff_zless_0";

Goal "[| x: int; y: int |] ==> (x = y) <-> (x$-y = #0)";
by (asm_simp_tac (simpset() addsimps zcompare_rls) 1);
qed "eq_iff_zdiff_eq_0";

Goal "(x $<= y) <-> (x$-y $<= #0)";
by (asm_simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zle_iff_zdiff_zle_0";


(** For combine_numerals **)

Goal "i$*u $+ (j$*u $+ k) = (i$+j)$*u $+ k";
by (simp_tac (simpset() addsimps [zadd_zmult_distrib]@zadd_ac) 1);
qed "left_zadd_zmult_distrib";


(** For cancel_numerals **)

val rel_iff_rel_0_rls = map (inst "y" "?u$+?v")
                          [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0] @
		        map (inst "y" "n")
                          [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0];

Goal "(i$*u $+ m = j$*u $+ n) <-> ((i$-j)$*u $+ m = intify(n))";
by (simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
by (simp_tac (simpset() addsimps zcompare_rls) 1);
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "eq_add_iff1";

Goal "(i$*u $+ m = j$*u $+ n) <-> (intify(m) = (j$-i)$*u $+ n)";
by (simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
by (simp_tac (simpset() addsimps zcompare_rls) 1);
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "eq_add_iff2";

Goal "(i$*u $+ m $< j$*u $+ n) <-> ((i$-j)$*u $+ m $< n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "less_add_iff1";

Goal "(i$*u $+ m $< j$*u $+ n) <-> (m $< (j$-i)$*u $+ n)";
by (asm_simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]@
                                     zadd_ac@rel_iff_rel_0_rls) 1);
qed "less_add_iff2";

Goal "(i$*u $+ m $<= j$*u $+ n) <-> ((i$-j)$*u $+ m $<= n)";
by (simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
by (simp_tac (simpset() addsimps zcompare_rls) 1);
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "le_add_iff1";

Goal "(i$*u $+ m $<= j$*u $+ n) <-> (m $<= (j$-i)$*u $+ n)";
by (simp_tac (simpset() addsimps [zdiff_def, zadd_zmult_distrib]) 1);
by (simp_tac (simpset() addsimps zcompare_rls) 1);
by (simp_tac (simpset() addsimps zadd_ac) 1);
qed "le_add_iff2";


structure Int_Numeral_Simprocs =
struct

(*Utilities*)

val integ_of_const = Const ("Bin.integ_of", iT --> iT);

fun mk_numeral n = integ_of_const $ NumeralSyntax.mk_bin n;

(*Decodes a binary INTEGER*)
fun dest_numeral (Const("Bin.integ_of", _) $ w) = 
     (NumeralSyntax.dest_bin w
      handle Match => raise TERM("Int_Numeral_Simprocs.dest_numeral:1", [w]))
  | dest_numeral t =  raise TERM("Int_Numeral_Simprocs.dest_numeral:2", [t]);

fun find_first_numeral past (t::terms) =
	((dest_numeral t, rev past @ terms)
	 handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val zero = mk_numeral 0;
val mk_plus = FOLogic.mk_binop "Int.zadd";

val iT = Ind_Syntax.iT;

val zminus_const = Const ("Int.zminus", iT --> iT);

(*Thus mk_sum[t] yields t+#0; longer sums don't have a trailing zero*)
fun mk_sum []        = zero
  | mk_sum [t,u]     = mk_plus (t, u)
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum []        = zero
  | long_mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

val dest_plus = FOLogic.dest_bin "Int.zadd" iT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const ("Int.zadd", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const ("Int.zdiff", _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
	if pos then t::ts else zminus_const$t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = FOLogic.mk_binop "Int.zdiff";
val dest_diff = FOLogic.dest_bin "Int.zdiff" iT;

val one = mk_numeral 1;
val mk_times = FOLogic.mk_binop "Int.zmult";

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts
                        else mk_times (t, mk_prod ts);

val dest_times = FOLogic.dest_bin "Int.zmult" iT;

fun dest_prod t =
      let val (t,u) = dest_times t 
      in  dest_prod t @ dest_prod u  end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*) 
fun mk_coeff (k, t) = mk_times (mk_numeral k, t);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const ("Int.zminus", _) $ t) = dest_coeff (~sign) t
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


(*Simplify #1*n and n*#1 to n*)
val add_0s = [zadd_0_intify, zadd_0_right_intify];

val mult_1s = [zmult_1_intify, zmult_1_right_intify, 
               zmult_minus1, zmult_minus1_right];

val tc_rules = [integ_of_type, intify_in_int, 
                int_of_type, zadd_type, zdiff_type, zmult_type] @ bin.intrs;
val intifys = [intify_ident, zadd_intify1, zadd_intify2,
               zdiff_intify1, zdiff_intify2, zmult_intify1, zmult_intify2,
               zless_intify1, zless_intify2, zle_intify1, zle_intify2];

(*To perform binary arithmetic*)
val bin_simps = [add_integ_of_left] @ bin_arith_simps @ bin_rel_simps;

(*To evaluate binary negations of coefficients*)
val zminus_simps = NCons_simps @
                   [integ_of_minus RS sym, 
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

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;
fun prep_pat s = Thm.read_cterm (Theory.sign_of (the_context ()))
                      (s, TypeInfer.anyT ["logic"]);
val prep_pats = map prep_pat;

structure CancelNumeralsCommon =
  struct
  val mk_sum    	= mk_sum
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val find_first_coeff	= find_first_coeff []
  val trans_tac		= ArithData.gen_trans_tac iff_trans
  val norm_tac_ss1 = ZF_ss addsimps add_0s@mult_1s@diff_simps@
                                    zminus_simps@zadd_ac
  val norm_tac_ss2 = ZF_ss addsimps bin_simps@int_mult_minus_simps@intifys
  val norm_tac_ss3 = ZF_ss addsimps int_minus_from_mult_simps@
                                    zadd_ac@zmult_ac@tc_rules@intifys
  val norm_tac		= ALLGOALS (asm_simp_tac norm_tac_ss1)
			  THEN ALLGOALS (asm_simp_tac norm_tac_ss2)
			  THEN ALLGOALS (asm_simp_tac norm_tac_ss3)
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (ZF_ss addsimps add_0s@bin_simps@tc_rules@intifys))
         THEN ALLGOALS Asm_simp_tac
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s@mult_1s)
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "inteq_cancel_numerals"
  val mk_bal   = FOLogic.mk_eq
  val dest_bal = FOLogic.dest_eq
  val bal_add1 = eq_add_iff1 RS iff_trans
  val bal_add2 = eq_add_iff2 RS iff_trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intless_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel "Int.zless"
  val dest_bal = FOLogic.dest_bin "Int.zless" iT
  val bal_add1 = less_add_iff1 RS iff_trans
  val bal_add2 = less_add_iff2 RS iff_trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = ArithData.prove_conv "intle_cancel_numerals"
  val mk_bal   = FOLogic.mk_binrel "Int.zle"
  val dest_bal = FOLogic.dest_bin "Int.zle" iT
  val bal_add1 = le_add_iff1 RS iff_trans
  val bal_add2 = le_add_iff2 RS iff_trans
);

val cancel_numerals = 
  map prep_simproc
   [("inteq_cancel_numerals",
     prep_pats ["l $+ m = n", "l = m $+ n", 
		"l $- m = n", "l = m $- n", 
		"l $* m = n", "l = m $* n"], 
     EqCancelNumerals.proc),
    ("intless_cancel_numerals", 
     prep_pats ["l $+ m $< n", "l $< m $+ n", 
		"l $- m $< n", "l $< m $- n", 
		"l $* m $< n", "l $< m $* n"], 
     LessCancelNumerals.proc),
    ("intle_cancel_numerals", 
     prep_pats ["l $+ m $<= n", "l $<= m $+ n", 
		"l $- m $<= n", "l $<= m $- n", 
		"l $* m $<= n", "l $<= m $* n"], 
     LeCancelNumerals.proc)];


(*version without the hyps argument*)
fun prove_conv_nohyps name tacs sg = ArithData.prove_conv name tacs sg [];

structure CombineNumeralsData =
  struct
  val add		= op + : int*int -> int 
  val mk_sum    	= long_mk_sum    (*to work for e.g. #2*x $+ #3*x *)
  val dest_sum		= dest_sum
  val mk_coeff		= mk_coeff
  val dest_coeff	= dest_coeff 1
  val left_distrib	= left_zadd_zmult_distrib RS trans
  val prove_conv        = prove_conv_nohyps "int_combine_numerals"
  val trans_tac         = ArithData.gen_trans_tac trans
  val norm_tac_ss1 = ZF_ss addsimps add_0s@mult_1s@diff_simps@
                                    zminus_simps@zadd_ac@intifys
  val norm_tac_ss2 = ZF_ss addsimps bin_simps@int_mult_minus_simps@intifys
  val norm_tac_ss3 = ZF_ss addsimps int_minus_from_mult_simps@
                                    zadd_ac@zmult_ac@tc_rules@intifys
  val norm_tac		= ALLGOALS (asm_simp_tac norm_tac_ss1)
			  THEN ALLGOALS (asm_simp_tac norm_tac_ss2)
			  THEN ALLGOALS (asm_simp_tac norm_tac_ss3)
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (ZF_ss addsimps add_0s@bin_simps@tc_rules@intifys))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (add_0s@mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);
  
val combine_numerals = 
    prep_simproc ("int_combine_numerals",
		  prep_pats ["i $+ j", "i $- j"],
		  CombineNumerals.proc);



(** Constant folding for integer multiplication **)

(*The trick is to regard products as sums, e.g. #3 $* x $* #4 as
  the "sum" of #3, x, #4; the literals are then multiplied*)


structure CombineNumeralsProdData =
  struct
  val add		= op * : int*int -> int
  val mk_sum    	= mk_prod
  val dest_sum		= dest_prod
  fun mk_coeff(k,t) = if t=one then mk_numeral k 
                      else raise TERM("mk_coeff", [])
  fun dest_coeff t = (dest_numeral t, one)  (*We ONLY want pure numerals.*)
  val left_distrib	= zmult_assoc RS sym RS trans
  val prove_conv        = prove_conv_nohyps "int_combine_numerals_prod"
  val trans_tac         = ArithData.gen_trans_tac trans
  val norm_tac_ss1 = ZF_ss addsimps mult_1s@diff_simps@zminus_simps
  val norm_tac_ss2 = ZF_ss addsimps [zmult_zminus_right RS sym]@
                                    bin_simps@zmult_ac@tc_rules@intifys
  val norm_tac		= ALLGOALS (asm_simp_tac norm_tac_ss1)
			  THEN ALLGOALS (asm_simp_tac norm_tac_ss2)
  val numeral_simp_tac	= 
         ALLGOALS (simp_tac (ZF_ss addsimps bin_simps@tc_rules@intifys))
  val simplify_meta_eq  = ArithData.simplify_meta_eq (mult_1s)
  end;


structure CombineNumeralsProd = CombineNumeralsFun(CombineNumeralsProdData);
  
val combine_numerals_prod = 
    prep_simproc ("int_combine_numerals_prod",
		  prep_pats ["i $* j"],
		  CombineNumeralsProd.proc);

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

