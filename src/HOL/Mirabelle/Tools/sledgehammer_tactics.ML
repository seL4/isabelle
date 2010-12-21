(*  Title:      sledgehammer_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010

Sledgehammer as a tactic.
*)

signature SLEDGEHAMMER_TACTICS =
sig
  val sledgehammer_with_metis_tac : Proof.context -> int -> tactic
  val sledgehammer_as_unsound_oracle_tac : Proof.context -> int -> tactic
  val sledgehammer_as_oracle_tac : Proof.context -> int -> tactic
end;

structure Sledgehammer_Tactics : SLEDGEHAMMER_TACTICS =
struct
  
fun run_atp force_full_types timeout i n ctxt goal name =
  let
    val chained_ths = [] (* a tactic has no chained ths *)
    val params as {type_sys, relevance_thresholds, max_relevant, ...} =
      ((if force_full_types then [("full_types", "true")] else [])
       @ [("timeout", Int.toString (Time.toSeconds timeout))])
       (* @ [("overlord", "true")] *)
      |> Sledgehammer_Isar.default_params ctxt
    val prover = Sledgehammer_Provers.get_prover ctxt false name
    val default_max_relevant =
      Sledgehammer_Provers.default_max_relevant_for_prover ctxt name
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt name
    val relevance_fudge =
      Sledgehammer_Provers.relevance_fudge_for_prover ctxt name
    val relevance_override = {add = [], del = [], only = false}
    val (_, hyp_ts, concl_t) = Sledgehammer_Util.strip_subgoal goal i
    val no_dangerous_types =
      Sledgehammer_ATP_Translate.types_dangerous_types type_sys
    val facts =
      Sledgehammer_Filter.relevant_facts ctxt no_dangerous_types
          relevance_thresholds
          (the_default default_max_relevant max_relevant) is_built_in_const
          relevance_fudge relevance_override chained_ths hyp_ts concl_t
    (* Check for constants other than the built-in HOL constants. If none of
       them appear (as should be the case for TPTP problems, unless "auto" or
       "simp" already did its "magic"), we can skip the relevance filter. *)
    val pure_goal =
      not (exists_Const (fn (s, _) => String.isSubstring "." s andalso
                                      not (String.isSubstring "HOL" s))
                        (prop_of goal))
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       facts = map Sledgehammer_Provers.Untranslated_Fact facts,
       smt_head = NONE}
  in
    (case prover params (K "") problem of
      {outcome = NONE, used_facts, ...} => used_facts |> map fst |> SOME
    | _ => NONE)
      handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

fun to_period ("." :: _) = []
  | to_period ("" :: ss) = to_period ss
  | to_period (s :: ss) = s :: to_period ss
  | to_period [] = []

val atp = "vampire" (* or "e" or "spass" etc. *)

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (ProofContext.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover=SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

fun sledgehammer_with_metis_tac ctxt i th =
  let
    val timeout = Time.fromSeconds 30
  in
    case run_atp false timeout i i ctxt th atp of
      SOME facts =>
      Metis_Tactics.metis_tac ctxt (maps (thms_of_name ctxt) facts) i th
    | NONE => Seq.empty
  end

fun generic_sledgehammer_as_oracle_tac force_full_types ctxt i th =
  let
    val thy = ProofContext.theory_of ctxt
    val timeout = Time.fromSeconds 30
    val xs = run_atp force_full_types timeout i i ctxt th atp
  in if is_some xs then Skip_Proof.cheat_tac thy th else Seq.empty end

val sledgehammer_as_unsound_oracle_tac =
  generic_sledgehammer_as_oracle_tac false
val sledgehammer_as_oracle_tac = generic_sledgehammer_as_oracle_tac true

end;
