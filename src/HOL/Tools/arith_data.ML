(*  Title:      HOL/Tools/arith_data.ML
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Common arithmetic proof auxiliary and legacy.
*)

signature ARITH_DATA =
sig
  val arith_tac: Proof.context -> int -> tactic
  val add_tactic: string -> (Proof.context -> int -> tactic) -> theory -> theory

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
  type T = (serial * (string * (Proof.context -> int -> tactic))) list;
  val empty = [];
  fun merge data : T = AList.merge (op =) (K true) data;
);

fun add_tactic name tac = Arith_Tactics.map (cons (serial (), (name, tac)));

fun arith_tac ctxt =
  let
    val tactics = Arith_Tactics.get (Proof_Context.theory_of ctxt);
    fun invoke (_, (_, tac)) k st = tac ctxt k st;
  in FIRST' (map invoke (rev tactics)) end;

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>arith\<close>
      (Scan.succeed (fn ctxt =>
        METHOD (fn facts =>
          HEADGOAL
            (Method.insert_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>arith\<close>) @ facts)
              THEN' arith_tac ctxt))))
      "various arithmetic decision procedures");


(* some specialized syntactic operations *)

fun mk_number T 1 = HOLogic.numeral_const T $ HOLogic.one_const
  | mk_number T n = HOLogic.mk_number T n;

(*Thus mk_sum[t] yields t+0; longer sums don't have a trailing zero*)
fun mk_sum T [] = mk_number T 0
  | mk_sum T [t, u] = \<^Const>\<open>plus T for t u\<close>
  | mk_sum T (t :: ts) = \<^Const>\<open>plus T for t \<open>mk_sum T ts\<close>\<close>;

(*this version ALWAYS includes a trailing zero*)
fun long_mk_sum T [] = mk_number T 0
  | long_mk_sum T (t :: ts) = \<^Const>\<open>plus T for t \<open>long_mk_sum T ts\<close>\<close>;

(*decompose additions AND subtractions as a sum*)
fun dest_summing pos \<^Const_>\<open>plus _ for t u\<close> ts = dest_summing pos t (dest_summing pos u ts)
  | dest_summing pos \<^Const_>\<open>minus _ for t u\<close> ts = dest_summing pos t (dest_summing (not pos) u ts)
  | dest_summing pos t ts = (if pos then t else \<^Const>\<open>uminus \<open>fastype_of t\<close> for t\<close>) :: ts;

fun dest_sum t = dest_summing true t [];


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
  ALLGOALS (safe_simp_tac (put_simpset HOL_ss ctxt |> Simplifier.add_simps rules));

fun simplify_meta_eq rules ctxt =
  simplify (put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps rules
    |> Simplifier.add_eqcong @{thm eq_cong2}) o mk_meta_eq;

end;
