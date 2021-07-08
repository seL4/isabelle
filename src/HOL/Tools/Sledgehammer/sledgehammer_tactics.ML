(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010, 2011

Sledgehammer as a tactic.
*)

signature SLEDGEHAMMER_TACTICS =
sig
  type fact_override = Sledgehammer_Fact.fact_override

  val sledgehammer_with_metis_tac : Proof.context -> (string * string) list -> fact_override ->
    thm list -> int -> tactic
  val sledgehammer_as_oracle_tac : Proof.context -> (string * string) list -> fact_override ->
    thm list -> int -> tactic
end;

structure Sledgehammer_Tactics : SLEDGEHAMMER_TACTICS =
struct

open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh
open Sledgehammer_Commands

fun run_prover override_params fact_override chained i n ctxt goal =
  let
    val thy = Proof_Context.theory_of ctxt
    val mode = Normal
    val params as {provers, induction_rules, max_facts, ...} = default_params thy override_params
    val name = hd provers
    val prover = get_prover ctxt mode name
    val default_max_facts = default_max_facts_of_prover ctxt name
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal i ctxt
    val keywords = Thy_Header.get_keywords' ctxt
    val css_table = clasimpset_rule_table_of ctxt
    val inst_inducts = induction_rules = SOME Instantiate
    val facts =
      nearly_all_facts ctxt inst_inducts fact_override keywords css_table chained hyp_ts concl_t
      |> relevant_facts ctxt params name (the_default default_max_facts max_facts) fact_override
        hyp_ts concl_t
      |> hd |> snd
    val problem =
      {comment = "", state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = n,
       factss = [("", facts)], found_proof = I}
  in
    (case prover params problem of
      {outcome = NONE, used_facts, ...} => used_facts |> map fst |> SOME
    | _ => NONE)
    handle ERROR message => (warning ("Error: " ^ message ^ "\n"); NONE)
  end

fun sledgehammer_with_metis_tac ctxt override_params fact_override chained i th =
  let val override_params = override_params @ [("preplay_timeout", "0")] in
    (case run_prover override_params fact_override chained i i ctxt th of
      SOME facts =>
      Metis_Tactic.metis_tac [] ATP_Problem_Generate.combs_or_liftingN ctxt
        (maps (thms_of_name ctxt) facts) i th
    | NONE => Seq.empty)
  end

fun sledgehammer_as_oracle_tac ctxt override_params fact_override chained i th =
  let
    val override_params =
      override_params @
      [("preplay_timeout", "0"),
       ("minimize", "false")]
    val xs = run_prover override_params fact_override chained i i ctxt th
  in
    if is_some xs then ALLGOALS (Skip_Proof.cheat_tac ctxt) th else Seq.empty
  end

end;
