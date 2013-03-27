(*  Title:      Pure/skip_proof.ML
    Author:     Makarius

Skip proof via oracle invocation.
*)

signature SKIP_PROOF =
sig
  val report: Proof.context -> unit
  val make_thm_cterm: cterm -> thm
  val make_thm: theory -> term -> thm
  val cheat_tac: theory -> tactic
end;

structure Skip_Proof: SKIP_PROOF =
struct

(* report *)

fun report ctxt =
  Context_Position.if_visible ctxt Output.report
    (Markup.markup Markup.bad "Skipped proof");


(* oracle setup *)

val (_, make_thm_cterm) =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (Binding.name "skip_proof", I)));

fun make_thm thy prop = make_thm_cterm (Thm.cterm_of thy prop);


(* cheat_tac *)

fun cheat_tac thy st =
  ALLGOALS (rtac (make_thm thy (Var (("A", 0), propT)))) st;

end;
