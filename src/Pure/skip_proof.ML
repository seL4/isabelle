(*  Title:      Pure/skip_proof.ML
    Author:     Makarius

Skip proof via oracle invocation.
*)

signature SKIP_PROOF =
sig
  val report: Proof.context -> unit
  val make_thm_cterm: cterm -> thm
  val make_thm: theory -> term -> thm
  val cheat_tac: Proof.context -> int -> tactic
end;

structure Skip_Proof: SKIP_PROOF =
struct

(* report *)

fun report ctxt =
  if Context_Position.is_visible ctxt then
    Output.report [Markup.markup (Markup.bad ()) "Skipped proof"]
  else ();


(* oracle setup *)

val (_, make_thm_cterm) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (Binding.make ("skip_proof", \<^here>), I)));

fun make_thm thy prop = make_thm_cterm (Thm.global_cterm_of thy prop);


(* cheat_tac -- 'sorry' *)

fun cheat_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val thy = Proof_Context.theory_of ctxt;
    val assms = Assumption.all_assms_of ctxt;
    val cheat = make_thm thy (Logic.list_implies (map Thm.term_of assms, goal));
    val thm = Drule.implies_elim_list cheat (map Thm.assume assms);
  in PRIMITIVE (Drule.with_subgoal i (Thm.elim_implies thm)) end);

end;
