(*  Title:      HOL/Tools/SMT2/verit_proof_parse.ML
    Author:     Mathias Fleury, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

VeriT proof parsing.
*)

signature VERIT_PROOF_PARSE =
sig
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  val parse_proof: Proof.context -> SMT2_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT2_Solver.parsed_proof
end;

structure VeriT_Proof_Parse: VERIT_PROOF_PARSE =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open VeriT_Isar
open VeriT_Proof

fun find_and_add_missing_dependances steps assms ll_offset =
  let
    fun prems_to_theorem_number [] id repl = (([], []), (id, repl))
      | prems_to_theorem_number (x :: ths) id replaced =
        (case Int.fromString (perhaps (try (unprefix SMTLIB2_Interface.assert_prefix)) x) of
          NONE =>
          let
            val ((prems, iidths), (id', replaced')) = prems_to_theorem_number ths id replaced
          in
            ((x :: prems, iidths), (id', replaced'))
          end
        | SOME th =>
          (case Option.map snd (List.find (fst #> curry (op =) x) replaced) of
            NONE =>
            let
              val id' = if th = ll_offset then 0 else id - ll_offset (* 0: for the conjecture*)
              val ((prems, iidths), (id'', replaced')) =
                prems_to_theorem_number ths (if th <> ll_offset then id + 1 else id)
                  ((x, string_of_int id') :: replaced)
            in
              ((string_of_int id' :: prems, (th, (id', th - ll_offset)) :: iidths),
               (id'', replaced'))
            end
          | SOME x =>
            let
              val ((prems, iidths), (id', replaced')) = prems_to_theorem_number ths id replaced
            in ((x :: prems, iidths), (id', replaced')) end))
    fun update_step (VeriT_Proof.VeriT_Step {prems, id = id0, rule = rule0,
        concl = concl0, fixes = fixes0}) (id, replaced) =
      let val ((prems', iidths), (id', replaced)) = prems_to_theorem_number prems id replaced
      in
        ((VeriT_Proof.VeriT_Step {id = id0, rule = rule0, prems = prems', concl = concl0,
           fixes = fixes0}, iidths), (id', replaced))
      end
  in
    fold_map update_step steps (1, [])
    |> fst
    |> `(map snd)
    ||> (map fst)
    |>> flat
    |>> map (fn (_, (id, tm_id)) => let val (i, tm) = nth assms tm_id in (i, (id, tm)) end)
  end

fun add_missing_steps iidths =
  let
    fun add_single_step (_, (id, th)) = VeriT_Proof.VeriT_Step {id = string_of_int id, rule = "input",
      prems = [], concl = prop_of th, fixes = []}
  in map add_single_step iidths end

fun parse_proof _
    ({context = ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT2_Translate.replay_data)
    xfacts prems concl output =
  let
    val (steps, _) = VeriT_Proof.parse typs terms output ctxt
    val (iidths, steps'') = find_and_add_missing_dependances steps assms (length ll_defs)
    val steps' = add_missing_steps iidths @ steps''
    fun id_of_index i = the_default ~1 (Option.map fst (AList.lookup (op =) iidths i))

    val prems_i = 1
    val facts_i = prems_i + length prems
    val conjecture_i = 0
    val ll_offset = id_of_index conjecture_i
    val prem_ids = map id_of_index (prems_i upto facts_i - 1)
    val helper_ids = map_filter (try (fn (~1, idth) => idth)) iidths

    val fact_ids = map_filter (fn (i, (id, _)) =>
      (try (apsnd (nth xfacts)) (id, i - facts_i))) iidths
    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, prop_of th)) helper_ids @
      map (fn (_, ((s, _), th)) => (s, prop_of th)) fact_ids
    val fact_helper_ids =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids @ map (apsnd (fst o fst)) fact_ids
  in
    {outcome = NONE, fact_ids = fact_ids,
     atp_proof = fn () => atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids ll_offset fact_helper_ids steps'}
  end

end;
