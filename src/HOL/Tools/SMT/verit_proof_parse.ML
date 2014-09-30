(*  Title:      HOL/Tools/SMT/verit_proof_parse.ML
    Author:     Mathias Fleury, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

VeriT proof parsing.
*)

signature VERIT_PROOF_PARSE =
sig
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  val parse_proof: Proof.context -> SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
end;

structure VeriT_Proof_Parse: VERIT_PROOF_PARSE =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open VeriT_Isar
open VeriT_Proof

fun add_used_assms_in_step (VeriT_Proof.VeriT_Step {prems, ...}) =
  union (op =) (map_filter (try SMTLIB_Interface.assert_index_of_name) prems)

fun step_of_assm (i, th) =
  VeriT_Proof.VeriT_Step {id = SMTLIB_Interface.assert_name_of_index i, rule = veriT_input_rule,
    prems = [], concl = prop_of th, fixes = []}

fun parse_proof _
    ({context = ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT_Translate.replay_data)
    xfacts prems concl output =
  let
    val (actual_steps, _) = VeriT_Proof.parse typs terms output ctxt
    val used_assm_ids = fold add_used_assms_in_step actual_steps []
    val used_assms = filter (member (op =) used_assm_ids o fst) assms
    val assm_steps = map step_of_assm used_assms
    val steps = assm_steps @ actual_steps

    val conjecture_i = length ll_defs
    val prems_i = conjecture_i + 1
    val num_prems = length prems
    val facts_i = prems_i + num_prems
    val num_facts = length xfacts
    val helpers_i = facts_i + num_facts

    val conjecture_id = conjecture_i
    val prem_ids = prems_i upto prems_i + num_prems - 1
    val fact_ids = facts_i upto facts_i + num_facts - 1
    val fact_ids' = map (fn i => (i, nth xfacts (i - facts_i))) fact_ids
    val helper_ids' = filter (fn (i, _) => i >= helpers_i) used_assms

    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, prop_of th)) helper_ids' @
      map (fn (_, ((s, _), th)) => (s, prop_of th)) fact_ids'
    val fact_helper_ids' =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids' @ map (apsnd (fst o fst)) fact_ids'
  in
    {outcome = NONE, fact_ids = fact_ids',
     atp_proof = fn () => atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids conjecture_id fact_helper_ids' steps}
  end

end;
