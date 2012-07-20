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

open Sledgehammer_Fact
open Sledgehammer_MaSh

val MePoN = "MePo"
val MaShN = "MaSh"
val MeshN = "Mesh"
val IsarN = "Isar"

val max_facts_slack = 2

val all_names =
  filter_out is_likely_tautology_or_too_meta
  #> map (rpair () o nickname_of) #> Symtab.make

fun evaluate_mash_suggestions ctxt params thy file_name =
  let
    val {provers, max_facts, slice, type_enc, lam_trans, timeout, ...} =
      Sledgehammer_Isar.default_params ctxt []
    val prover = hd provers
    val slack_max_facts = max_facts_slack * the max_facts
    val path = file_name |> Path.explode
    val lines = path |> File.read_lines
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val facts = all_facts_of (Proof_Context.init_global thy) css_table
    val all_names = all_names (facts |> map snd)
    val mepo_ok = Unsynchronized.ref 0
    val mash_ok = Unsynchronized.ref 0
    val mesh_ok = Unsynchronized.ref 0
    val isar_ok = Unsynchronized.ref 0
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
    fun solve_goal (j, line) =
      let
        val (name, suggs) = extract_query line
        val th =
          case find_first (fn (_, th) => nickname_of th = name) facts of
            SOME (_, th) => th
          | NONE => error ("No fact called \"" ^ name ^ "\"")
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val isar_deps = isar_dependencies_of all_names th
        val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
        val mepo_facts =
          Sledgehammer_MePo.iterative_relevant_facts ctxt params prover
              slack_max_facts NONE hyp_ts concl_t facts
        val mash_facts = facts |> suggested_facts suggs
        val mess = [(mepo_facts, []), (mash_facts, [])]
        val mesh_facts = mesh_facts slack_max_facts mess
        val isar_facts = suggested_facts isar_deps facts
        fun prove ok heading facts =
          let
            val facts =
              facts
              |> Sledgehammer_Fact.maybe_instantiate_inducts ctxt hyp_ts concl_t
              |> take (the max_facts)
            val res as {outcome, ...} =
              run_prover_for_mash ctxt params prover facts goal
            val _ = if is_none outcome then ok := !ok + 1 else ()
          in str_of_res heading facts res end
        val mepo_s = prove mepo_ok MePoN mepo_facts
        val mash_s = prove mash_ok MaShN mash_facts
        val mesh_s = prove mesh_ok MeshN mesh_facts
        val isar_s = prove isar_ok IsarN isar_facts
      in
        ["Goal " ^ string_of_int j ^ ": " ^ name, mepo_s, mash_s, mesh_s,
         isar_s]
        |> cat_lines |> tracing
      end
    fun total_of heading ok n =
      "  " ^ heading ^ ": " ^ string_of_int (!ok) ^ " (" ^
      Real.fmt (StringCvt.FIX (SOME 1))
               (100.0 * Real.fromInt (!ok) / Real.fromInt n) ^ "%)"
    val inst_inducts = Config.get ctxt Sledgehammer_Fact.instantiate_inducts
    val options =
      [prover, string_of_int (the max_facts) ^ " facts",
       "slice" |> not slice ? prefix "dont_", the_default "smart" type_enc,
       the_default "smart" lam_trans, ATP_Util.string_from_time timeout,
       "instantiate_inducts" |> not inst_inducts ? prefix "dont_"]
    val n = length lines
  in
    tracing " * * *";
    tracing ("Options: " ^ commas options);
    List.app solve_goal (tag_list 1 lines);
    ["Successes (of " ^ string_of_int n ^ " goals)",
     total_of MePoN mepo_ok n,
     total_of MaShN mash_ok n,
     total_of MeshN mesh_ok n,
     total_of IsarN isar_ok n]
    |> cat_lines |> tracing
  end

end;
