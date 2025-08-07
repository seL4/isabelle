(*  Title:      HOL/Library/Cancellation/cancel_data.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Mathias Fleury, MPII

Datastructure for the cancelation simprocs.
*)

signature CANCEL_DATA =
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

structure Cancel_Data : CANCEL_DATA =
struct

(*** Utilities ***)

(*No reordering of the arguments.*)
fun fast_mk_iterate_add (n, mset) =
  \<^Const>\<open>iterate_add \<open>fastype_of mset\<close> for n mset\<close>;

(*iterate_add is not symmetric, unlike multiplication over natural numbers.*)
fun mk_iterate_add (t, u) =
  (if fastype_of t = \<^typ>\<open>nat\<close> then (t, u) else (u, t))
  |> fast_mk_iterate_add;

(*Maps n to #n for n = 1, 2*)
val numeral_syms =
  map (fn th => th RS sym) @{thms numeral_One numeral_2_eq_2 numeral_1_eq_Suc_0};

val numeral_sym_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context> |> Simplifier.add_simps numeral_syms);

fun mk_number 1 = HOLogic.numeral_const HOLogic.natT $ HOLogic.one_const
  | mk_number n = HOLogic.mk_number HOLogic.natT n;
fun dest_number t = Int.max (0, snd (HOLogic.dest_number t));

fun find_first_numeral past (t::terms) =
    ((dest_number t, t, rev past @ terms)
    handle TERM _ => find_first_numeral (t::past) terms)
  | find_first_numeral _ [] = raise TERM("find_first_numeral", []);

fun typed_zero T = \<^Const>\<open>Groups.zero T\<close>;
fun typed_one T = \<^Const>\<open>numeral T for \<^Const>\<open>num.One\<close>\<close>;
val mk_plus = HOLogic.mk_binop \<^const_name>\<open>plus\<close>;

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero.*)
fun mk_sum T [] = typed_zero T
  | mk_sum _ [t,u] = mk_plus (t, u)
  | mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

val dest_plus = HOLogic.dest_bin \<^const_name>\<open>plus\<close> dummyT;


(*** Other simproc items ***)

val bin_simps =
  (@{thm numeral_One} RS sym) ::
  @{thms add_numeral_left diff_nat_numeral diff_0_eq_0 mult_numeral_left(1)
      if_True if_False not_False_eq_True nat_0 nat_numeral nat_neg_numeral iterate_add_simps(1)
      iterate_add_empty arith_simps rel_simps of_nat_numeral};


(*** CancelNumerals simprocs ***)

val one = mk_number 1;

fun mk_prod T [] = typed_one T
  | mk_prod _ [t] = t
  | mk_prod T (t :: ts) = if t = one then mk_prod T ts else mk_iterate_add (t, mk_prod T ts);

val dest_iterate_add = HOLogic.dest_bin \<^const_name>\<open>iterate_add\<close> dummyT;

fun dest_iterate_adds t =
  let val (t,u) = dest_iterate_add t in
    t :: dest_iterate_adds u end
  handle TERM _ => [t];

fun mk_coeff (k,t) = mk_iterate_add (mk_number k, t);

(*Express t as a product of (possibly) a numeral with other factors, sorted*)
fun dest_coeff t =
  let
    val T = fastype_of t
    val ts = sort Term_Ord.term_ord (dest_iterate_adds t);
    val (n, _, ts') =
      find_first_numeral [] ts
      handle TERM _ => (1, one, ts);
  in (n, mk_prod T ts') end;

(*Find first coefficient-term THAT MATCHES u*)
fun find_first_coeff _ _ [] = raise TERM("find_first_coeff", [])
  | find_first_coeff past u (t::terms) =
    let val (n,u') = dest_coeff t in
      if u aconv u' then (n, rev past @ terms) else find_first_coeff (t::past) u terms end
    handle TERM _ => find_first_coeff (t::past) u terms;

(*
  Split up a sum into the list of its constituent terms.
*)
fun dest_summation (t, ts) =
    let val (t1,t2) = dest_plus t in
      dest_summation (t1, dest_summation (t2, ts)) end
    handle TERM _ => t :: ts;

fun dest_sum t = dest_summation (t, []);

val rename_numerals = simplify (put_simpset numeral_sym_ss \<^context>) o Thm.transfer \<^theory>;

(*Simplify \<open>iterate_add (Suc 0) n\<close>, \<open>iterate_add n (Suc 0)\<close>, \<open>n+0\<close>, and \<open>0+n\<close> to \<open>n\<close>*)
val add_0s  = map rename_numerals @{thms monoid_add_class.add_0_left monoid_add_class.add_0_right};
val mult_1s = map rename_numerals @{thms iterate_add_1 iterate_add_simps(2)[of 0]};

(*And these help the simproc return False when appropriate. We use the same list as the
simproc for natural numbers, but adapted.*)
fun contra_rules ctxt =
  @{thms le_zero_eq}  @ Named_Theorems.get ctxt \<^named_theorems>\<open>cancelation_simproc_eq_elim\<close>;

fun simplify_meta_eq ctxt =
  Arith_Data.simplify_meta_eq
    (@{thms numeral_1_eq_Suc_0 Nat.add_0_right
         mult_0 mult_0_right mult_1 mult_1_right iterate_add_Numeral1 of_nat_numeral
         monoid_add_class.add_0_left iterate_add_simps(1) monoid_add_class.add_0_right
         iterate_add_Numeral1} @
     contra_rules ctxt) ctxt;

val mk_sum = mk_sum;
val dest_sum = dest_sum;
val mk_coeff = mk_coeff;
val dest_coeff = dest_coeff;
val find_first_coeff = find_first_coeff [];
val trans_tac = Numeral_Simprocs.trans_tac;

val norm_ss1 =
  simpset_of (put_simpset Numeral_Simprocs.num_ss \<^context>
    |> Simplifier.add_simps (numeral_syms @ add_0s @ mult_1s @ @{thms ac_simps iterate_add_simps}));

val norm_ss2 =
  simpset_of (put_simpset Numeral_Simprocs.num_ss \<^context>
    |> Simplifier.add_simps (bin_simps @ @{thms ac_simps}));

fun norm_tac ctxt =
  ALLGOALS (simp_tac (put_simpset norm_ss1 ctxt))
  THEN ALLGOALS (simp_tac (put_simpset norm_ss2 ctxt));

val mset_simps_ss =
  simpset_of (put_simpset HOL_basic_ss \<^context> |> Simplifier.add_simps bin_simps);

fun numeral_simp_tac ctxt = ALLGOALS (simp_tac (put_simpset mset_simps_ss ctxt));

val simplify_meta_eq = simplify_meta_eq;
val prove_conv = Arith_Data.prove_conv;

end

