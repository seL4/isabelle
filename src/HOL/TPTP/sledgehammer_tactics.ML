(*  Title:      HOL/TPTP/sledgehammer_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010, 2011

Sledgehammer as a tactic.
*)

signature SLEDGEHAMMER_TACTICS =
sig
  type fact_override = Sledgehammer_Fact.fact_override

  val sledgehammer_with_metis_tac :
    Proof.context -> (string * string) list -> fact_override -> int -> tactic
  val sledgehammer_as_oracle_tac :
    Proof.context -> (string * string) list -> fact_override -> int -> tactic
end;

structure Sledgehammer_Tactics : SLEDGEHAMMER_TACTICS =
struct

open Sledgehammer_Fact

fun run_prover override_params fact_override i n ctxt goal =
  let
    val mode = Sledgehammer_Provers.Normal
    val params as {provers, max_relevant, slice, ...} =
      Sledgehammer_Isar.default_params ctxt override_params
    val name = hd provers
    val prover = Sledgehammer_Provers.get_prover ctxt mode name
    val default_max_relevant =
      Sledgehammer_Provers.default_max_relevant_for_prover ctxt slice name
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal i
    val ho_atp = exists (Sledgehammer_Provers.is_ho_atp ctxt) provers
    val facts =
      Sledgehammer_Fact.nearly_all_facts ctxt ho_atp fact_override []
                                         hyp_ts concl_t
      |> Sledgehammer_Filter_MaSh.relevant_facts ctxt params name
             (the_default default_max_relevant max_relevant) fact_override
             hyp_ts concl_t
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       facts = facts |> map (apfst (apfst (fn name => name ())))
                     |> map Sledgehammer_Provers.Untranslated_Fact}
  in
    (case prover params (K (K (K ""))) problem of
      {outcome = NONE, used_facts, ...} => used_facts |> map fst |> SOME
    | _ => NONE)
      handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover=SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

fun sledgehammer_with_metis_tac ctxt override_params fact_override i th =
  let val override_params = override_params @ [("preplay_timeout", "0")] in
    case run_prover override_params fact_override i i ctxt th of
      SOME facts =>
      Metis_Tactic.metis_tac [] ATP_Problem_Generate.combs_or_liftingN ctxt
          (maps (thms_of_name ctxt) facts) i th
    | NONE => Seq.empty
  end

fun sledgehammer_as_oracle_tac ctxt override_params fact_override i th =
  let
    val thy = Proof_Context.theory_of ctxt
    val override_params =
      override_params @
      [("preplay_timeout", "0"),
       ("minimize", "false")]
    val xs = run_prover override_params fact_override i i ctxt th
  in if is_some xs then Skip_Proof.cheat_tac thy th else Seq.empty end

end;
