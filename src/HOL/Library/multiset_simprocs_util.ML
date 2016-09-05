(* Author: Mathias Fleury, MPII


Datatructure for the cancelation simprocs for multisets, based on Larry Paulson's simprocs for
natural numbers and numerals.
*)
signature MULTISET_CANCEL_COMMON =
sig
  val mk_sum : typ -> term list -> term
  val dest_sum : term -> term list
  val mk_coeff : int * term -> term
  val dest_coeff : term -> int * term
  val find_first_coeff : term -> term list -> int * term list
  val trans_tac : Proof.context -> thm option -> tactic

  val norm_ss1 : simpset
  val norm_ss2: simpset
  val norm_tac: Proof.context -> tactic

  val numeral_simp_tac : Proof.context -> tactic
  val simplify_meta_eq : Proof.context -> thm -> thm
  val prove_conv : tactic list -> Proof.context -> thm list -> term * term -> thm option
end;

structure Multiset_Cancel_Common : MULTISET_CANCEL_COMMON =
struct

(*** Utilities ***)

fun mk_repeat_mset (t, u) =
  let
    val T = fastype_of t;
    val U = fastype_of u;
  in Const (@{const_name "repeat_mset"}, T --> U --> U) $ t $ u end;

(*Maps n to #n for n = 1, 2*)
val numeral_syms = [@{thm numeral_One} RS sym, @{thm numeral_2_eq_2} RS sym,
  @{thm numeral_1_eq_Suc_0} RS sym];

val numeral_sym_ss =
  simpset_of (put_simpset HOL_basic_ss @{context} addsimps  numeral_syms);

fun mk_number 1 = HOLogic.numeral_const HOLogic.natT $ HOLogic.one_const
  | mk_number n = HOLogic.mk_number HOLogic.natT n
fun dest_number t = Int.max (0, snd (HOLogic.dest_number t));

fun find_first_numeral past (t::terms) =
    ((dest_number t, t, rev past @ terms)
    handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral _ [] = raise TERM("find_first_numeral", []);

fun typed_zero T = Const (@{const_name "Groups.zero"}, T);
val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero.*)
fun mk_sum T [] = typed_zero T
  | mk_sum _ [t,u] = mk_plus (t, u)
  | mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

val dest_plus = HOLogic.dest_bin @{const_name Groups.plus} dummyT;


(*** Other simproc items ***)

val bin_simps =
  [@{thm numeral_One} RS sym,
   @{thm add_numeral_left},
   @{thm diff_nat_numeral}, @{thm diff_0_eq_0}, @{thm diff_0},
   @{thm mult_numeral_left(1)},
   @{thm if_True}, @{thm if_False}, @{thm not_False_eq_True},
   @{thm nat_0}, @{thm nat_numeral}, @{thm nat_neg_numeral},
   @{thm add_mset_commute}, @{thm repeat_mset.simps(1)}] @
  @{thms arith_simps} @ @{thms rel_simps};


(*** CancelNumerals simprocs ***)

val one = mk_number 1;

fun mk_prod [] = one
  | mk_prod [t] = t
  | mk_prod (t :: ts) = if t = one then mk_prod ts else mk_repeat_mset (t, mk_prod ts);

val dest_repeat_mset = HOLogic.dest_bin @{const_name Multiset.repeat_mset} dummyT

fun dest_repeat_msets t =
  let val (t,u) = dest_repeat_mset t in
    t :: dest_repeat_msets u end
  handle TERM _ => [t];

fun mk_coeff (k,t) = mk_repeat_mset (mk_number k, t);

(*Express t as a product of (possibly) a numeral with other factors, sorted*)
fun dest_coeff t =
  let
    val ts = sort Term_Ord.term_ord (dest_repeat_msets t);
    val (n, _, ts') =
      find_first_numeral [] ts
      handle TERM _ => (1, one, ts);
  in (n, mk_prod ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff _ _ [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
    let val (n,u') = dest_coeff t in
      if u aconv u' then (n, rev past @ terms) else find_first_coeff (t::past) u terms end
    handle TERM _ => find_first_coeff (t::past) u terms;

(*Split up a sum into the list of its constituent terms, on the way replace all the
\<open>add_mset a C\<close> by \<open>add_mset a {#}\<close> and \<open>C\<close>, iff C was not already the empty set*)
fun dest_add_mset (Const (@{const_name add_mset},  typ) $ a $
      Const (@{const_name "Groups.zero_class.zero"}, typ'), ts) =
    Const (@{const_name add_mset},  typ) $ a $ typed_zero typ' :: ts
  | dest_add_mset (Const (@{const_name add_mset},  typ) $ a $ mset, ts) =
    dest_add_mset (mset, Const (@{const_name add_mset}, typ) $ a $
      typed_zero (fastype_of mset) :: ts)
  | dest_add_mset (t, ts) =
    let val (t1,t2) = dest_plus t in
      dest_add_mset (t1, dest_add_mset (t2, ts)) end
    handle TERM _ => (t::ts);

fun dest_add_mset_sum t = dest_add_mset (t, []);

val rename_numerals = simplify (put_simpset numeral_sym_ss @{context}) o Thm.transfer @{theory};

(*Simplify \<open>repeat_mset (Suc 0) n\<close>, \<open>n+0\<close>, and \<open>0+n\<close> to \<open>n\<close>*)
val add_0s  = map rename_numerals [@{thm Groups.add_0}, @{thm Groups.add_0_right}];
val mult_1s = map rename_numerals @{thms repeat_mset.simps(2)[of 0]};


(*And these help the simproc return False when appropriate. We use the same list as the nat
version.*)
val contra_rules =
  [@{thm union_mset_add_mset_left}, @{thm union_mset_add_mset_right},
   @{thm empty_not_add_mset}, @{thm add_mset_not_empty},
   @{thm subset_mset.le_zero_eq}, @{thm le_zero_eq}];

val simplify_meta_eq =
  Arith_Data.simplify_meta_eq
    ([@{thm numeral_1_eq_Suc_0}, @{thm Nat.add_0}, @{thm Nat.add_0_right},
      @{thm mult_0}, @{thm mult_0_right}, @{thm mult_1}, @{thm mult_1_right},
      @{thm Groups.add_0}, @{thm repeat_mset.simps(1)},
      @{thm monoid_add_class.add_0_right}] @
     contra_rules);

val mk_sum = mk_sum;
val dest_sum = dest_add_mset_sum;
val mk_coeff = mk_coeff;
val dest_coeff = dest_coeff;
val find_first_coeff = find_first_coeff [];
val trans_tac = Numeral_Simprocs.trans_tac;

val norm_ss1 =
  simpset_of (put_simpset Numeral_Simprocs.num_ss @{context} addsimps
    numeral_syms @ add_0s @ mult_1s @ @{thms ac_simps});

val norm_ss2 =
  simpset_of (put_simpset Numeral_Simprocs.num_ss @{context} addsimps
    bin_simps @
    [@{thm union_mset_add_mset_left},
     @{thm union_mset_add_mset_right}] @
    @{thms ac_simps});

fun norm_tac ctxt =
  ALLGOALS (simp_tac (put_simpset norm_ss1 ctxt))
  THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt));

val mset_simps_ss =
  simpset_of (put_simpset HOL_basic_ss @{context} addsimps bin_simps);

fun numeral_simp_tac ctxt = ALLGOALS (simp_tac (put_simpset mset_simps_ss ctxt));

val simplify_meta_eq = simplify_meta_eq;
val prove_conv = Arith_Data.prove_conv;

end
