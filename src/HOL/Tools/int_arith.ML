(* Authors: Larry Paulson and Tobias Nipkow

Simprocs and decision procedure for numerals and linear arithmetic.
*)

structure Int_Numeral_Simprocs =
struct

(** Utilities **)

fun mk_number T n = HOLogic.number_of_const T $ HOLogic.mk_numeral n;

fun find_first_numeral past (t::terms) =
        ((snd (HOLogic.dest_number t), rev past @ terms)
         handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral past [] = raise TERM("find_first_numeral", []);

val mk_plus = HOLogic.mk_binop @{const_name HOL.plus};

fun mk_minus t = 
  let val T = Term.fastype_of t
  in Const (@{const_name HOL.uminus}, T --> T) $ t end;

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum T []        = mk_number T 0
  | mk_sum T [t,u]     = mk_plus (t, u)
  | mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum T []        = mk_number T 0
  | long_mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

val dest_plus = HOLogic.dest_bin @{const_name HOL.plus} Term.dummyT;

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const (@{const_name HOL.plus}, _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const (@{const_name HOL.minus}, _) $ t $ u, ts) =
        dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) =
        if pos then t::ts else mk_minus t :: ts;

fun dest_sum t = dest_summing (true, t, []);

val mk_diff = HOLogic.mk_binop @{const_name HOL.minus};
val dest_diff = HOLogic.dest_bin @{const_name HOL.minus} Term.dummyT;

val mk_times = HOLogic.mk_binop @{const_name HOL.times};

fun one_of T = Const(@{const_name HOL.one},T);

(* build product with trailing 1 rather than Numeral 1 in order to avoid the
   unnecessary restriction to type class number_ring
   which is not required for cancellation of common factors in divisions.
*)
fun mk_prod T = 
  let val one = one_of T
  fun mk [] = one
    | mk [t] = t
    | mk (t :: ts) = if t = one then mk ts else mk_times (t, mk ts)
  in mk end;

(*This version ALWAYS includes a trailing one*)
fun long_mk_prod T []        = one_of T
  | long_mk_prod T (t :: ts) = mk_times (t, mk_prod T ts);

val dest_times = HOLogic.dest_bin @{const_name HOL.times} Term.dummyT;

fun dest_prod t =
      let val (t,u) = dest_times t
      in dest_prod t @ dest_prod u end
      handle TERM _ => [t];

(*DON'T do the obvious simplifications; that would create special cases*)
fun mk_coeff (k, t) = mk_times (mk_number (Term.fastype_of t) k, t);

(*Express t as a product of (possibly) a numeral with other sorted terms*)
fun dest_coeff sign (Const (@{const_name HOL.uminus}, _) $ t) = dest_coeff (~sign) t
  | dest_coeff sign t =
    let val ts = sort TermOrd.term_ord (dest_prod t)
        val (n, ts') = find_first_numeral [] ts
                          handle TERM _ => (1, ts)
    in (sign*n, mk_prod (Term.fastype_of t) ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff past u [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
        let val (n,u') = dest_coeff 1 t
        in if u aconv u' then (n, rev past @ terms)
                         else find_first_coeff (t::past) u terms
        end
        handle TERM _ => find_first_coeff (t::past) u terms;

(*Fractions as pairs of ints. Can't use Rat.rat because the representation
  needs to preserve negative values in the denominator.*)
fun mk_frac (p, q) = if q = 0 then raise Div else (p, q);

(*Don't reduce fractions; sums must be proved by rule add_frac_eq.
  Fractions are reduced later by the cancel_numeral_factor simproc.*)
fun add_frac ((p1, q1), (p2, q2)) = (p1 * q2 + p2 * q1, q1 * q2);

val mk_divide = HOLogic.mk_binop @{const_name HOL.divide};

(*Build term (p / q) * t*)
fun mk_fcoeff ((p, q), t) =
  let val T = Term.fastype_of t
  in mk_times (mk_divide (mk_number T p, mk_number T q), t) end;

(*Express t as a product of a fraction with other sorted terms*)
fun dest_fcoeff sign (Const (@{const_name HOL.uminus}, _) $ t) = dest_fcoeff (~sign) t
  | dest_fcoeff sign (Const (@{const_name HOL.divide}, _) $ t $ u) =
    let val (p, t') = dest_coeff sign t
        val (q, u') = dest_coeff 1 u
    in (mk_frac (p, q), mk_divide (t', u')) end
  | dest_fcoeff sign t =
    let val (p, t') = dest_coeff sign t
        val T = Term.fastype_of t
    in (mk_frac (p, 1), mk_divide (t', one_of T)) end;


(** New term ordering so that AC-rewriting brings numerals to the front **)

(*Order integers by absolute value and then by sign. The standard integer
  ordering is not well-founded.*)
fun num_ord (i,j) =
  (case int_ord (abs i, abs j) of
    EQUAL => int_ord (Int.sign i, Int.sign j) 
  | ord => ord);

(*This resembles TermOrd.term_ord, but it puts binary numerals before other
  non-atomic terms.*)
local open Term 
in 
fun numterm_ord (Abs (_, T, t), Abs(_, U, u)) =
      (case numterm_ord (t, u) of EQUAL => TermOrd.typ_ord (T, U) | ord => ord)
  | numterm_ord
     (Const(@{const_name Int.number_of}, _) $ v, Const(@{const_name Int.number_of}, _) $ w) =
     num_ord (HOLogic.dest_numeral v, HOLogic.dest_numeral w)
  | numterm_ord (Const(@{const_name Int.number_of}, _) $ _, _) = LESS
  | numterm_ord (_, Const(@{const_name Int.number_of}, _) $ _) = GREATER
  | numterm_ord (t, u) =
      (case int_ord (size_of_term t, size_of_term u) of
        EQUAL =>
          let val (f, ts) = strip_comb t and (g, us) = strip_comb u in
            (case TermOrd.hd_ord (f, g) of EQUAL => numterms_ord (ts, us) | ord => ord)
          end
      | ord => ord)
and numterms_ord (ts, us) = list_ord numterm_ord (ts, us)
end;

fun numtermless tu = (numterm_ord tu = LESS);

val num_ss = HOL_ss settermless numtermless;

(*Maps 0 to Numeral0 and 1 to Numeral1 so that arithmetic isn't complicated by the abstract 0 and 1.*)
val numeral_syms = [@{thm numeral_0_eq_0} RS sym, @{thm numeral_1_eq_1} RS sym];

(*Simplify Numeral0+n, n+Numeral0, Numeral1*n, n*Numeral1, 1*x, x*1, x/1 *)
val add_0s =  @{thms add_0s};
val mult_1s = @{thms mult_1s mult_1_left mult_1_right divide_1};

(*Simplify inverse Numeral1, a/Numeral1*)
val inverse_1s = [@{thm inverse_numeral_1}];
val divide_1s = [@{thm divide_numeral_1}];

(*To perform binary arithmetic.  The "left" rewriting handles patterns
  created by the Int_Numeral_Simprocs, such as 3 * (5 * x). *)
val simps = [@{thm numeral_0_eq_0} RS sym, @{thm numeral_1_eq_1} RS sym,
                 @{thm add_number_of_left}, @{thm mult_number_of_left}] @
                @{thms arith_simps} @ @{thms rel_simps};

(*Binary arithmetic BUT NOT ADDITION since it may collapse adjacent terms
  during re-arrangement*)
val non_add_simps =
  subtract Thm.eq_thm [@{thm add_number_of_left}, @{thm number_of_add} RS sym] simps;

(*To evaluate binary negations of coefficients*)
val minus_simps = [@{thm numeral_m1_eq_minus_1} RS sym, @{thm number_of_minus} RS sym] @
                   @{thms minus_bin_simps} @ @{thms pred_bin_simps};

(*To let us treat subtraction as addition*)
val diff_simps = [@{thm diff_minus}, @{thm minus_add_distrib}, @{thm minus_minus}];

(*To let us treat division as multiplication*)
val divide_simps = [@{thm divide_inverse}, @{thm inverse_mult_distrib}, @{thm inverse_inverse_eq}];

(*push the unary minus down: - x * y = x * - y *)
val minus_mult_eq_1_to_2 =
    [@{thm mult_minus_left}, @{thm minus_mult_right}] MRS trans |> standard;

(*to extract again any uncancelled minuses*)
val minus_from_mult_simps =
    [@{thm minus_minus}, @{thm mult_minus_left}, @{thm mult_minus_right}];

(*combine unary minus with numeric literals, however nested within a product*)
val mult_minus_simps =
    [@{thm mult_assoc}, @{thm minus_mult_left}, minus_mult_eq_1_to_2];

val norm_ss1 = num_ss addsimps numeral_syms @ add_0s @ mult_1s @
  diff_simps @ minus_simps @ @{thms add_ac}
val norm_ss2 = num_ss addsimps non_add_simps @ mult_minus_simps
val norm_ss3 = num_ss addsimps minus_from_mult_simps @ @{thms add_ac} @ @{thms mult_ac}

structure CancelNumeralsCommon =
  struct
  val mk_sum            = mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val find_first_coeff  = find_first_coeff []
  val trans_tac         = K Arith_Data.trans_tac

  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = HOL_ss addsimps add_0s @ simps
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq (add_0s @ mult_1s)
  end;


structure EqCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin "op =" Term.dummyT
  val bal_add1 = @{thm eq_add_iff1} RS trans
  val bal_add2 = @{thm eq_add_iff2} RS trans
);

structure LessCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less} Term.dummyT
  val bal_add1 = @{thm less_add_iff1} RS trans
  val bal_add2 = @{thm less_add_iff2} RS trans
);

structure LeCancelNumerals = CancelNumeralsFun
 (open CancelNumeralsCommon
  val prove_conv = Arith_Data.prove_conv
  val mk_bal   = HOLogic.mk_binrel @{const_name HOL.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less_eq} Term.dummyT
  val bal_add1 = @{thm le_add_iff1} RS trans
  val bal_add2 = @{thm le_add_iff2} RS trans
);

val cancel_numerals =
  map Arith_Data.prep_simproc
   [("inteq_cancel_numerals",
     ["(l::'a::number_ring) + m = n",
      "(l::'a::number_ring) = m + n",
      "(l::'a::number_ring) - m = n",
      "(l::'a::number_ring) = m - n",
      "(l::'a::number_ring) * m = n",
      "(l::'a::number_ring) = m * n"],
     K EqCancelNumerals.proc),
    ("intless_cancel_numerals",
     ["(l::'a::{ordered_idom,number_ring}) + m < n",
      "(l::'a::{ordered_idom,number_ring}) < m + n",
      "(l::'a::{ordered_idom,number_ring}) - m < n",
      "(l::'a::{ordered_idom,number_ring}) < m - n",
      "(l::'a::{ordered_idom,number_ring}) * m < n",
      "(l::'a::{ordered_idom,number_ring}) < m * n"],
     K LessCancelNumerals.proc),
    ("intle_cancel_numerals",
     ["(l::'a::{ordered_idom,number_ring}) + m <= n",
      "(l::'a::{ordered_idom,number_ring}) <= m + n",
      "(l::'a::{ordered_idom,number_ring}) - m <= n",
      "(l::'a::{ordered_idom,number_ring}) <= m - n",
      "(l::'a::{ordered_idom,number_ring}) * m <= n",
      "(l::'a::{ordered_idom,number_ring}) <= m * n"],
     K LeCancelNumerals.proc)];


structure CombineNumeralsData =
  struct
  type coeff            = int
  val iszero            = (fn x => x = 0)
  val add               = op +
  val mk_sum            = long_mk_sum    (*to work for e.g. 2*x + 3*x *)
  val dest_sum          = dest_sum
  val mk_coeff          = mk_coeff
  val dest_coeff        = dest_coeff 1
  val left_distrib      = @{thm combine_common_factor} RS trans
  val prove_conv        = Arith_Data.prove_conv_nohyps
  val trans_tac         = K Arith_Data.trans_tac

  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = HOL_ss addsimps add_0s @ simps
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq (add_0s @ mult_1s)
  end;

structure CombineNumerals = CombineNumeralsFun(CombineNumeralsData);

(*Version for fields, where coefficients can be fractions*)
structure FieldCombineNumeralsData =
  struct
  type coeff            = int * int
  val iszero            = (fn (p, q) => p = 0)
  val add               = add_frac
  val mk_sum            = long_mk_sum
  val dest_sum          = dest_sum
  val mk_coeff          = mk_fcoeff
  val dest_coeff        = dest_fcoeff 1
  val left_distrib      = @{thm combine_common_factor} RS trans
  val prove_conv        = Arith_Data.prove_conv_nohyps
  val trans_tac         = K Arith_Data.trans_tac

  val norm_ss1a = norm_ss1 addsimps inverse_1s @ divide_simps
  fun norm_tac ss =
    ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss1a))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss2))
    THEN ALLGOALS (simp_tac (Simplifier.inherit_context ss norm_ss3))

  val numeral_simp_ss = HOL_ss addsimps add_0s @ simps @ [@{thm add_frac_eq}]
  fun numeral_simp_tac ss = ALLGOALS (simp_tac (Simplifier.inherit_context ss numeral_simp_ss))
  val simplify_meta_eq = Arith_Data.simplify_meta_eq (add_0s @ mult_1s @ divide_1s)
  end;

structure FieldCombineNumerals = CombineNumeralsFun(FieldCombineNumeralsData);

val combine_numerals =
  Arith_Data.prep_simproc
    ("int_combine_numerals", 
     ["(i::'a::number_ring) + j", "(i::'a::number_ring) - j"], 
     K CombineNumerals.proc);

val field_combine_numerals =
  Arith_Data.prep_simproc
    ("field_combine_numerals", 
     ["(i::'a::{number_ring,field,division_by_zero}) + j",
      "(i::'a::{number_ring,field,division_by_zero}) - j"], 
     K FieldCombineNumerals.proc);

(** Constant folding for multiplication in semirings **)

(*We do not need folding for addition: combine_numerals does the same thing*)

structure Semiring_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val assoc_ss = HOL_ss addsimps @{thms mult_ac}
  val eq_reflection = eq_reflection
  fun is_numeral (Const(@{const_name Int.number_of}, _) $ _) = true
    | is_numeral _ = false;
end;

structure Semiring_Times_Assoc = Assoc_Fold (Semiring_Times_Assoc_Data);

val assoc_fold_simproc =
  Arith_Data.prep_simproc
   ("semiring_assoc_fold", ["(a::'a::comm_semiring_1_cancel) * b"],
    K Semiring_Times_Assoc.proc);

end;

Addsimprocs Int_Numeral_Simprocs.cancel_numerals;
Addsimprocs [Int_Numeral_Simprocs.combine_numerals];
Addsimprocs [Int_Numeral_Simprocs.field_combine_numerals];
Addsimprocs [Int_Numeral_Simprocs.assoc_fold_simproc];

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

(*** decision procedure for linear arithmetic ***)

(*---------------------------------------------------------------------------*)
(* Linear arithmetic                                                         *)
(*---------------------------------------------------------------------------*)

(*
Instantiation of the generic linear arithmetic package for int.
*)

structure Int_Arith =
struct

(* Update parameters of arithmetic prover *)

(* reduce contradictory =/</<= to False *)

(* Evaluation of terms of the form "m R n" where R is one of "=", "<=" or "<",
   and m and n are ground terms over rings (roughly speaking).
   That is, m and n consist only of 1s combined with "+", "-" and "*".
*)

val zeroth = (symmetric o mk_meta_eq) @{thm of_int_0};

val lhss0 = [@{cpat "0::?'a::ring"}];

fun proc0 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] zeroth)
  end;

val zero_to_of_int_zero_simproc =
  make_simproc {lhss = lhss0, name = "zero_to_of_int_zero_simproc",
  proc = proc0, identifier = []};

val oneth = (symmetric o mk_meta_eq) @{thm of_int_1};

val lhss1 = [@{cpat "1::?'a::ring_1"}];

fun proc1 phi ss ct =
  let val T = ctyp_of_term ct
  in if typ_of T = @{typ int} then NONE else
     SOME (instantiate' [SOME T] [] oneth)
  end;

val one_to_of_int_one_simproc =
  make_simproc {lhss = lhss1, name = "one_to_of_int_one_simproc",
  proc = proc1, identifier = []};

val allowed_consts =
  [@{const_name "op ="}, @{const_name "HOL.times"}, @{const_name "HOL.uminus"},
   @{const_name "HOL.minus"}, @{const_name "HOL.plus"},
   @{const_name "HOL.zero"}, @{const_name "HOL.one"}, @{const_name "HOL.less"},
   @{const_name "HOL.less_eq"}];

fun check t = case t of
   Const(s,t) => if s = @{const_name "HOL.one"} then not (t = @{typ int})
                else s mem_string allowed_consts
 | a$b => check a andalso check b
 | _ => false;

val conv =
  Simplifier.rewrite
   (HOL_basic_ss addsimps
     ((map (fn th => th RS sym) [@{thm of_int_add}, @{thm of_int_mult},
             @{thm of_int_diff},  @{thm of_int_minus}])@
      [@{thm of_int_less_iff}, @{thm of_int_le_iff}, @{thm of_int_eq_iff}])
     addsimprocs [zero_to_of_int_zero_simproc,one_to_of_int_one_simproc]);

fun sproc phi ss ct = if check (term_of ct) then SOME (conv ct) else NONE

val lhss' =
  [@{cpat "(?x::?'a::ring_char_0) = (?y::?'a)"},
   @{cpat "(?x::?'a::ordered_idom) < (?y::?'a)"},
   @{cpat "(?x::?'a::ordered_idom) <= (?y::?'a)"}]

val zero_one_idom_simproc =
  make_simproc {lhss = lhss' , name = "zero_one_idom_simproc",
  proc = sproc, identifier = []}

val add_rules =
    simp_thms @ @{thms arith_simps} @ @{thms rel_simps} @ @{thms arith_special} @
    @{thms int_arith_rules}

val nat_inj_thms = [@{thm zle_int} RS iffD2, @{thm int_int_eq} RS iffD2]

val int_numeral_base_simprocs = Int_Numeral_Simprocs.assoc_fold_simproc :: zero_one_idom_simproc
  :: Int_Numeral_Simprocs.combine_numerals
  :: Int_Numeral_Simprocs.cancel_numerals;

val setup =
  Lin_Arith.map_data (fn {add_mono_thms, mult_mono_thms, inj_thms, lessD, neqE, simpset} =>
   {add_mono_thms = add_mono_thms,
    mult_mono_thms = @{thm mult_strict_left_mono} :: @{thm mult_left_mono} :: mult_mono_thms,
    inj_thms = nat_inj_thms @ inj_thms,
    lessD = lessD @ [@{thm zless_imp_add1_zle}],
    neqE = neqE,
    simpset = simpset addsimps add_rules
                      addsimprocs int_numeral_base_simprocs
                      addcongs [if_weak_cong]}) #>
  arith_inj_const (@{const_name of_nat}, HOLogic.natT --> HOLogic.intT) #>
  arith_discrete @{type_name Int.int}

val fast_int_arith_simproc =
  Simplifier.simproc (the_context ())
  "fast_int_arith" 
     ["(m::'a::{ordered_idom,number_ring}) < n",
      "(m::'a::{ordered_idom,number_ring}) <= n",
      "(m::'a::{ordered_idom,number_ring}) = n"] (K Lin_Arith.lin_arith_simproc);

end;

Addsimprocs [Int_Arith.fast_int_arith_simproc];
