(*  Title:      HOL/TPTP/mash_eval.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Evaluate proof suggestions from MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EVAL =
sig
  type params = Sledgehammer_Provers.params

  val evaluate_mash_suggestions :
    Proof.context -> params -> theory -> string -> unit
end;

structure MaSh_Eval : MASH_EVAL =
struct

open Sledgehammer_Filter_MaSh

val isarN = "Isa"
val iterN = "Iter"
val mashN = "MaSh"
val meshN = "Mesh"

val max_facts_slack = 2

fun evaluate_mash_suggestions ctxt params thy file_name =
  let
    val {provers, max_facts, slice, type_enc, lam_trans, timeout, ...} =
      Sledgehammer_Isar.default_params ctxt []
    val prover_name = hd provers
    val path = file_name |> Path.explode
    val lines = path |> File.read_lines
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val facts = all_non_tautological_facts_of thy css_table
    val all_names = facts |> map (Thm.get_name_hint o snd)
    val iter_ok = Unsynchronized.ref 0
    val mash_ok = Unsynchronized.ref 0
    val mesh_ok = Unsynchronized.ref 0
    val isar_ok = Unsynchronized.ref 0
    fun find_sugg facts sugg =
      find_first (fn (_, th) => Thm.get_name_hint th = sugg) facts
    fun sugg_facts hyp_ts concl_t facts =
      map_filter (find_sugg facts)
      #> take (max_facts_slack * the max_facts)
      #> Sledgehammer_Fact.maybe_instantiate_inducts ctxt hyp_ts concl_t
    fun mesh_facts fsp =
      let
        val (fs1, fs2) =
          fsp |> pairself (map (apfst (apfst (fn name => name ()))))
        val fact_eq = (op =) o pairself fst
        fun score_in f fs =
          case find_index (curry fact_eq f) fs of
            ~1 => length fs
          | j => j
        fun score_of f = score_in f fs1 + score_in f fs2
      in
        union fact_eq fs1 fs2
        |> map (`score_of) |> sort (int_ord o pairself fst) |> map snd
        |> take (the max_facts)
        |> map (apfst (apfst K))
      end
    fun with_index facts s = (find_index (curry (op =) s) facts + 1, s)
    fun index_string (j, s) = s ^ "@" ^ string_of_int j
    fun str_of_res label facts {outcome, run_time, used_facts, ...} =
      let val facts = facts |> map (fn ((name, _), _) => name ()) in
        "  " ^ label ^ ": " ^
        (if is_none outcome then
           "Success (" ^ ATP_Util.string_from_time run_time ^ "): " ^
           (used_facts |> map (with_index facts o fst)
                       |> sort (int_ord o pairself fst)
                       |> map index_string
                       |> space_implode " ") ^
           (if length facts < the max_facts then
              " (of " ^ string_of_int (length facts) ^ ")"
            else
              "")
         else
           "Failure: " ^
           (facts |> take (the max_facts) |> tag_list 1
                  |> map index_string
                  |> space_implode " "))
      end
    fun prove ok heading facts goal =
      let
        val facts = facts |> take (the max_facts)
        val res as {outcome, ...} = run_prover ctxt params facts goal
        val _ = if is_none outcome then ok := !ok + 1 else ()
      in str_of_res heading facts res end
    fun solve_goal j name suggs =
      let
        val th =
          case find_first (fn (_, th) => Thm.get_name_hint th = name) facts of
            SOME (_, th) => th
          | NONE => error ("No fact called \"" ^ name ^ "\"")
        val isar_deps = isabelle_dependencies_of all_names th
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
        val isar_facts = sugg_facts hyp_ts concl_t facts isar_deps
        val iter_facts =
          Sledgehammer_Filter_Iter.iterative_relevant_facts ctxt params
              prover_name (max_facts_slack * the max_facts) NONE hyp_ts concl_t
              facts
        val mash_facts = sugg_facts hyp_ts concl_t facts suggs
        val mesh_facts = mesh_facts (iter_facts, mash_facts)
        val iter_s = prove iter_ok iterN iter_facts goal
        val mash_s = prove mash_ok mashN mash_facts goal
        val mesh_s = prove mesh_ok meshN mesh_facts goal
        val isar_s = prove isar_ok isarN isar_facts goal
      in
        ["Goal " ^ string_of_int j ^ ": " ^ name, iter_s, mash_s, mesh_s,
         isar_s]
        |> cat_lines |> tracing
      end
    val explode_suggs =
      space_explode " " #> filter_out (curry (op =) "") #> map unescape_meta
    fun do_line (j, line) =
      case space_explode ":" line of
        [goal_name, suggs] =>
        solve_goal j (unescape_meta goal_name) (explode_suggs suggs)
      | _ => ()
    fun total_of heading ok n =
      " " ^ heading ^ ": " ^ string_of_int (!ok) ^ " (" ^
      Real.fmt (StringCvt.FIX (SOME 1))
               (100.0 * Real.fromInt (!ok) / Real.fromInt n) ^ "%)"
    val inst_inducts = Config.get ctxt Sledgehammer_Fact.instantiate_inducts
    val options =
      [prover_name, string_of_int (the max_facts) ^ " facts",
       "slice" |> not slice ? prefix "dont_", the_default "smart" type_enc,
       the_default "smart" lam_trans, ATP_Util.string_from_time timeout,
       "instantiate_inducts" |> not inst_inducts ? prefix "dont_"]
    val n = length lines
  in
    tracing " * * *";
    tracing ("Options: " ^ commas options);
    List.app do_line (tag_list 1 lines);
    ["Successes (of " ^ string_of_int n ^ " goals)",
     total_of iterN iter_ok n,
     total_of mashN mash_ok n,
     total_of meshN mesh_ok n,
     total_of isarN isar_ok n]
    |> cat_lines |> tracing
  end

end;
