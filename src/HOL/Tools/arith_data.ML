(*  Title:      HOL/Tools/arith_data.ML
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Common arithmetic proof auxiliary and legacy.
*)

signature ARITH_DATA =
sig
  val arith_tac: Proof.context -> int -> tactic
  val verbose_arith_tac: Proof.context -> int -> tactic
  val add_tactic: string -> (bool -> Proof.context -> int -> tactic) -> theory -> theory
  val get_arith_facts: Proof.context -> thm list

  val mk_number: typ -> int -> term
  val mk_sum: typ -> term list -> term
  val long_mk_sum: typ -> term list -> term
  val dest_sum: term -> term list

  val prove_conv_nohyps: tactic list -> Proof.context -> term * term -> thm option
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val prove_conv2: tactic -> (simpset -> tactic) -> simpset -> term * term -> thm
  val simp_all_tac: thm list -> simpset -> tactic
  val simplify_meta_eq: thm list -> simpset -> thm -> thm

  val setup: theory -> theory
end;

structure Arith_Data: ARITH_DATA =
struct

(* slots for plugging in arithmetic facts and tactics *)

structure Arith_Facts = Named_Thms
(
  val name = @{binding arith}
  val description = "arith facts -- only ground formulas"
);

val get_arith_facts = Arith_Facts.get;

structure Arith_Tactics = Theory_Data
(
  type T = (serial * (string * (bool -> Proof.context -> int -> tactic))) list;
  val empty = [];
  val extend = I;
  fun merge data : T = AList.merge (op =) (K true) data;
);

fun add_tactic name tac = Arith_Tactics.map (cons (serial (), (name, tac)));

fun gen_arith_tac verbose ctxt =
  let
    val tactics = Arith_Tactics.get (Proof_Context.theory_of ctxt);
    fun invoke (_, (name, tac)) k st = tac verbose ctxt k st;
  in FIRST' (map invoke (rev tactics)) end;

val arith_tac = gen_arith_tac false;
val verbose_arith_tac = gen_arith_tac true;

val setup =
  Arith_Facts.setup #>
  Method.setup @{binding arith}
    (Scan.succeed (fn ctxt =>
      METHOD (fn facts => HEADGOAL (Method.insert_tac (get_arith_facts ctxt @ facts)
        THEN' verbose_arith_tac ctxt))))
    "various arithmetic decision procedures";


(* some specialized syntactic operations *)

fun mk_number T 1 = HOLogic.numeral_const T $ HOLogic.one_const
  | mk_number T n = HOLogic.mk_number T n;

val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};

fun mk_minus t = 
  let val T = Term.fastype_of t
  in Const (@{const_name Groups.uminus}, T --> T) $ t end;

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum T [] = mk_number T 0
  | mk_sum T [t, u] = mk_plus (t, u)
  | mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum T [] = mk_number T 0
  | long_mk_sum T (t :: ts) = mk_plus (t, mk_sum T ts);

(*decompose additions AND subtractions as a sum*)
fun dest_summing (pos, Const (@{const_name Groups.plus}, _) $ t $ u, ts) =
      dest_summing (pos, t, dest_summing (pos, u, ts))
  | dest_summing (pos, Const (@{const_name Groups.minus}, _) $ t $ u, ts) =
      dest_summing (pos, t, dest_summing (not pos, u, ts))
  | dest_summing (pos, t, ts) = (if pos then t else mk_minus t) :: ts;

fun dest_sum t = dest_summing (true, t, []);


(* various auxiliary and legacy *)

fun prove_conv_nohyps tacs ctxt (t, u) =
  if t aconv u then NONE
  else let val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))
  in SOME (Goal.prove ctxt [] [] eq (K (EVERY tacs))) end;

fun prove_conv tacs ctxt (_: thm list) = prove_conv_nohyps tacs ctxt;

fun prove_conv2 expand_tac norm_tac ss tu = (* FIXME avoid Drule.export_without_context *)
  mk_meta_eq (Drule.export_without_context (Goal.prove (Simplifier.the_context ss) [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ss]))));

fun simp_all_tac rules =
  let val ss0 = HOL_ss addsimps rules
      val safe_simp_tac = generic_simp_tac true (false, false, false)
  in fn ss => ALLGOALS (safe_simp_tac (Simplifier.inherit_context ss ss0)) end;

fun simplify_meta_eq rules =
  let val ss0 = HOL_basic_ss addsimps rules |> Simplifier.add_eqcong @{thm eq_cong2}
  in fn ss => simplify (Simplifier.inherit_context ss ss0) o mk_meta_eq end

end;
