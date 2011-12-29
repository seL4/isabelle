(*  Title:      Pure/Isar/skip_proof.ML
    Author:     Markus Wenzel, TU Muenchen

Skipping proofs -- via oracle (in quick and dirty mode) or by forking
(parallel mode).
*)

signature SKIP_PROOF =
sig
  val make_thm_cterm: cterm -> thm
  val make_thm: theory -> term -> thm
  val cheat_tac: theory -> tactic
  val prove: Proof.context -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
  val prove_global: theory -> string list -> term list -> term ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm
end;

structure Skip_Proof: SKIP_PROOF =
struct

(* oracle setup *)

val (_, make_thm_cterm) =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (Binding.name "skip_proof", I)));

fun make_thm thy prop = make_thm_cterm (Thm.cterm_of thy prop);


(* basic cheating *)

fun cheat_tac thy st =
  ALLGOALS (Tactic.rtac (make_thm thy (Var (("A", 0), propT)))) st;

fun prove ctxt xs asms prop tac =
  if ! quick_and_dirty then
    Goal.prove ctxt xs asms prop (fn _ => cheat_tac (Proof_Context.theory_of ctxt))
  else (if Goal.future_enabled () then Goal.prove_future else Goal.prove) ctxt xs asms prop tac;

fun prove_global thy xs asms prop tac =
  Drule.export_without_context (prove (Proof_Context.init_global thy) xs asms prop tac);

end;
