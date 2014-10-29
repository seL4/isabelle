(*  Title:      HOL/Tools/arith_data.ML
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Common arithmetic proof auxiliary and legacy.
*)

signature ARITH_DATA =
sig
  val arith_tac: Proof.context -> int -> tactic
  val verbose_arith_tac: Proof.context -> int -> tactic
  val add_tactic: string -> (bool -> Proof.context -> int -> tactic) -> theory -> theory

  val mk_number: typ -> int -> term
  val mk_sum: typ -> term list -> term
  val long_mk_sum: typ -> term list -> term
  val dest_sum: term -> term list

  val prove_conv_nohyps: tactic list -> Proof.context -> term * term -> thm option
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val prove_conv2: tactic -> (Proof.context -> tactic) -> Proof.context -> term * term -> thm
  val simp_all_tac: thm list -> Proof.context -> tactic
  val simplify_meta_eq: thm list -> Proof.context -> thm -> thm
end;

structure Arith_Data: ARITH_DATA =
struct

(* slot for plugging in tactics *)

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
    fun invoke (_, (_, tac)) k st = tac verbose ctxt k st;
  in FIRST' (map invoke (rev tactics)) end;

val arith_tac = gen_arith_tac false;
val verbose_arith_tac = gen_arith_tac true;

val _ =
  Theory.setup
    (Method.setup @{binding arith}
      (Scan.succeed (fn ctxt =>
        METHOD (fn facts =>
          HEADGOAL
          (Method.insert_tac (rev (Named_Theorems.get ctxt @{named_theorems arith}) @ facts)
            THEN' verbose_arith_tac ctxt))))
      "various arithmetic decision procedures");


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

fun prove_conv2 expand_tac norm_tac ctxt tu = (* FIXME avoid Drule.export_without_context *)
  mk_meta_eq (Drule.export_without_context (Goal.prove ctxt [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ctxt]))));

fun simp_all_tac rules ctxt =
  ALLGOALS (safe_simp_tac (put_simpset HOL_ss ctxt addsimps rules));

fun simplify_meta_eq rules ctxt =
  simplify (put_simpset HOL_basic_ss ctxt addsimps rules |> Simplifier.add_eqcong @{thm eq_cong2})
    o mk_meta_eq;

end;
