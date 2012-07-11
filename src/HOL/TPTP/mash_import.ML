(*  Title:      HOL/TPTP/mash_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import proof suggestions from MaSh (Machine-learning for Sledgehammer) and
evaluate them.
*)

signature MASH_IMPORT =
sig
  val import_and_evaluate_mash_suggestions :
    Proof.context -> theory -> string -> unit
end;

structure MaSh_Import : MASH_IMPORT =
struct

open MaSh_Export

val unescape_meta =
  let
    fun un accum [] = String.implode (rev accum)
      | un accum (#"\\" :: d1 :: d2 :: d3 :: cs) =
        (case Int.fromString (String.implode [d1, d2, d3]) of
           SOME n => un (Char.chr n :: accum) cs
         | NONE => "" (* error *))
      | un _ (#"\\" :: _) = "" (* error *)
      | un accum (c :: cs) = un (c :: accum) cs
  in un [] o String.explode end

val of_fact_name = unescape_meta

val max_relevant_slack = 2

fun import_and_evaluate_mash_suggestions ctxt thy file_name =
  let
    val params as {provers, max_relevant, relevance_thresholds, ...} =
      Sledgehammer_Isar.default_params ctxt []
    val prover_name = hd provers
    val path = file_name |> Path.explode
    val lines = path |> File.read_lines
    val facts = non_tautological_facts_of thy
    val all_names = facts |> map (Thm.get_name_hint o snd)
    val i = 1
    fun find_sugg facts sugg =
      find_first (fn (_, th) => Thm.get_name_hint th = sugg) facts
    fun sugg_facts hyp_ts concl_t facts =
      map_filter (find_sugg facts o of_fact_name)
      #> take (max_relevant_slack * the max_relevant)
      #> Sledgehammer_Filter.maybe_instantiate_inducts ctxt hyp_ts concl_t
      #> map (apfst (apfst (fn name => name ())))
    fun hybrid_facts fs1 fs2 =
      let
        val fact_eq = (op =) o pairself fst
        fun score_in f fs =
          case find_index (curry fact_eq f) fs of
            ~1 => length fs
          | j => j
        fun score_of f = score_in f fs1 + score_in f fs2
      in
        union fact_eq fs1 fs2
        |> map (`score_of) |> sort (int_ord o pairself fst) |> map snd
        |> take (the max_relevant)
      end
    fun with_index facts s =
      (find_index (fn ((s', _), _) => s = s') facts + 1, s)
    fun index_string (j, s) = s ^ "@" ^ string_of_int j
    fun str_of_res label facts {outcome, run_time, used_facts, ...} =
      "  " ^ label ^ ": " ^
      (if is_none outcome then
         "Success (" ^ ATP_Util.string_from_time run_time ^ "): " ^
         space_implode " " (used_facts |> map (with_index facts o fst)
                                       |> sort (int_ord o pairself fst)
                                       |> map index_string)
       else
         "Failure: " ^ space_implode " " (map (fst o fst) facts))
    fun run_sh heading facts goal =
      let
        val problem =
          {state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = 1,
           facts = facts |> map Sledgehammer_Provers.Untranslated_Fact}
        val prover =
          Sledgehammer_Run.get_minimizing_prover ctxt
              Sledgehammer_Provers.Normal prover_name
        val res as {outcome, ...} = prover params (K (K (K ""))) problem
      in (str_of_res heading facts res, is_none outcome) end
    fun solve_goal name suggs =
      let
        val name = of_fact_name name
        val th =
          case find_first (fn (_, th) => Thm.get_name_hint th = name) facts of
            SOME (_, th) => th
          | NONE => error ("No fact called \"" ^ name ^ "\"")
        val deps = dependencies_of all_names th
        val goal = goal_of_thm th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal i
        val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
        val deps_facts = sugg_facts hyp_ts concl_t facts deps
        val meng_facts =
          meng_paulson_facts ctxt prover_name
              (max_relevant_slack * the max_relevant) relevance_thresholds goal
              i facts
        val mash_facts = sugg_facts hyp_ts concl_t facts suggs
        val hybrid_facts = hybrid_facts meng_facts mash_facts
        val (dep_s, dep_ok) = run_sh "Dependencies" deps_facts goal
        val (meng_s, meng_ok) = run_sh "Meng & Paulson" meng_facts goal
        val (mash_s, mash_ok) = run_sh "MaSh" mash_facts goal
        val (hybrid_s, hybrid_ok) = run_sh "Hybrid" hybrid_facts goal
      in
        tracing (cat_lines ["Goal: ", name, dep_s, meng_s, mash_s, hybrid_s])
      end
    val explode_suggs = space_explode " " #> filter_out (curry (op =) "")
    fun do_line line =
      case space_explode ":" line of
        [goal_name, suggs] => solve_goal goal_name (explode_suggs suggs)
      | _ => ()
  in List.app do_line lines end

end;
