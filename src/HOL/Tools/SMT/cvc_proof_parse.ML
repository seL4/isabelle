(*  Title:      HOL/Tools/SMT/cvc_proof_parse.ML
    Author:     Jasmin Blanchette, TU Muenchen

CVC4 and cvc5 proof (actually, unsat core) parsing.
*)

signature CVC_PROOF_PARSE =
sig
  val parse_proof: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
  val parse_proof_lethe: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
  val cvc_matching_assms: Proof.context -> thm list -> term list -> term -> thm -> bool

end;

structure CVC_Proof_Parse: CVC_PROOF_PARSE =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open Lethe_Isar
open Lethe_Proof

(*taken from verit*)
fun add_used_asserts_in_step (Lethe_Proof.Lethe_Step {prems, ...}) =
  union (op =) (map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) prems)

fun cvc_matching_assms ctxt rewrite_rules ll_defs th th' =
  let
    val expand =
       not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
       #> Object_Logic.dest_judgment ctxt o (Thm.cterm_of ctxt)
       #> Thm.eta_long_conversion
       #> Thm.prop_of
       #> snd o Logic.dest_equals
       #> Simplifier.rewrite_term (Proof_Context.theory_of
          (empty_simpset ctxt |> Simplifier.add_simps rewrite_rules (*@ @{thms eq_True} still useful?*))) rewrite_rules []


    val normalize = 
       Object_Logic.dest_judgment ctxt o (Thm.cprop_of)
       #> Thm.eta_long_conversion
       #> Thm.prop_of
       #> snd o Logic.dest_equals
       #> Simplifier.rewrite_term (Proof_Context.theory_of
          (empty_simpset ctxt |> Simplifier.add_simps (rewrite_rules @ @{thms eq_True}))) rewrite_rules []
  in (expand th) aconv (normalize th') end

fun parse_proof_unsatcore ({ll_defs, assms, ...} : SMT_Translate.replay_data) xfacts prems _ output =
  if exists (String.isPrefix "(error \"This build of CVC4 doesn't have proof support") output then
    {outcome = NONE, fact_ids = NONE, atp_proof = K []}
  else
    let
      val num_ll_defs = length ll_defs

      val id_of_index = Integer.add num_ll_defs
      val index_of_id = Integer.add (~ num_ll_defs)

      val used_assert_ids =
        map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) output
      val used_assm_js =
        map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
          used_assert_ids

      val conjecture_i = 0
      val prems_i = conjecture_i + 1
      val num_prems = length prems
      val facts_i = prems_i + num_prems

      val fact_ids' =
        map_filter (fn j =>
          let val ((i, _), _) = nth assms j in
            try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
          end) used_assm_js
    in
      {outcome = NONE, fact_ids = SOME fact_ids', atp_proof = K []}
    end


fun parse_proof_lethe
    ({context = ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT_Translate.replay_data)
    xfacts prems concl output =
   if exists (String.isPrefix "(error \"This build of CVC4 doesn't have proof support") output then
     {outcome = NONE, fact_ids = NONE, atp_proof = K []}
   else
     let
    val num_ll_defs = length ll_defs
    val id_of_index = Integer.add num_ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)

    fun step_of_assume i ((_, role), th) =
      let
        val th = Thm.prop_of th
        fun matching (_, th') = cvc_matching_assms ctxt rewrite_rules ll_defs th th'
      in
        case List.find matching assms of
          NONE => []
        | SOME (k, _) =>
          Lethe_Proof.Lethe_Step 
           {id = SMTLIB_Interface.assert_name_of_role_and_index role (id_of_index i),
            rule = input_rule, prems = [], proof_ctxt = [], concl = th, fixes = []}
          |> single
      end

    val (actual_steps, _) = Lethe_Proof.parse typs terms output ctxt
    val used_assert_ids = fold add_used_asserts_in_step actual_steps []
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
        used_assert_ids
    val used_assms = map (nth assms) used_assm_js
    val assm_steps = map2 step_of_assume used_assm_js used_assms
        |> flat
    val steps = assm_steps @ actual_steps

    val conjecture_i = 0
    val prems_i = conjecture_i + 1
    val num_prems = length prems
    val facts_i = prems_i + num_prems
    val num_facts = length xfacts
    val helpers_i = facts_i + num_facts

    val conjecture_id = id_of_index conjecture_i
    val prem_ids = map id_of_index (prems_i upto prems_i + num_prems - 1)
    val fact_ids' =
      map_filter (fn j =>
        let val ((i, _), _) = nth assms j in
          try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
        end) used_assm_js
    val helper_ids' =
      map_filter (fn ((i, _), thm) => if i >= helpers_i then SOME (i, thm) else NONE) used_assms

    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, Thm.prop_of th)) helper_ids' @
      map (fn (_, ((s, _), th)) => (s, Thm.prop_of th)) fact_ids'
    val fact_helper_ids' =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids' @ map (apsnd (fst o fst)) fact_ids'
  in
    {outcome = NONE, fact_ids = SOME fact_ids',
     atp_proof = fn () => atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids conjecture_id fact_helper_ids' steps}
  end

fun parse_proof (rep as {context = ctxt, ...}) =
  if SMT_Config.use_lethe_proof_from_cvc ctxt
  then parse_proof_unsatcore rep
  else parse_proof_unsatcore rep

end;
