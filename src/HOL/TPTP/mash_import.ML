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

val depN = "Dependencies"
val mengN = "Meng & Paulson"
val mashN = "MaSh"
val meng_mashN = "M&P+MaSh"

val max_relevant_slack = 2

fun import_and_evaluate_mash_suggestions ctxt thy file_name =
  let
    val {provers, max_relevant, slice, type_enc, lam_trans, timeout, ...} =
      Sledgehammer_Isar.default_params ctxt []
    val prover_name = hd provers
    val path = file_name |> Path.explode
    val lines = path |> File.read_lines
    val facts = non_tautological_facts_of thy
    val all_names = facts |> map (Thm.get_name_hint o snd)
    val meng_ok = Unsynchronized.ref 0
    val mash_ok = Unsynchronized.ref 0
    val meng_mash_ok = Unsynchronized.ref 0
    val dep_ok = Unsynchronized.ref 0
    fun find_sugg facts sugg =
      find_first (fn (_, th) => Thm.get_name_hint th = sugg) facts
    fun sugg_facts hyp_ts concl_t facts =
      map_filter (find_sugg facts o of_fact_name)
      #> take (max_relevant_slack * the max_relevant)
      #> Sledgehammer_Filter.maybe_instantiate_inducts ctxt hyp_ts concl_t
      #> map (apfst (apfst (fn name => name ())))
    fun meng_mash_facts fs1 fs2 =
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
         (used_facts |> map (with_index facts o fst)
                     |> sort (int_ord o pairself fst)
                     |> map index_string
                     |> space_implode " ") ^
         (if length facts < the max_relevant then
            " (of " ^ string_of_int (length facts) ^ ")"
          else
            "")
       else
         "Failure: " ^
         (facts |> map (fst o fst)
                |> take (the max_relevant)
                |> tag_list 1
                |> map index_string
                |> space_implode " "))
    fun run_sh ok heading facts goal =
      let
        val facts = facts |> take (the max_relevant)
        val res as {outcome, ...} = run_sledgehammer ctxt facts goal
        val _ = if is_none outcome then ok := !ok + 1 else ()
      in str_of_res heading facts res end
    fun solve_goal j name suggs =
      let
        val name = of_fact_name name
        val th =
          case find_first (fn (_, th) => Thm.get_name_hint th = name) facts of
            SOME (_, th) => th
          | NONE => error ("No fact called \"" ^ name ^ "\"")
        val deps = dependencies_of all_names th
        val goal = goal_of_thm th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
        val deps_facts = sugg_facts hyp_ts concl_t facts deps
        val meng_facts =
          meng_paulson_facts ctxt (max_relevant_slack * the max_relevant) goal
                             facts
        val mash_facts = sugg_facts hyp_ts concl_t facts suggs
        val meng_mash_facts = meng_mash_facts meng_facts mash_facts
        val meng_s = run_sh meng_ok mengN meng_facts goal
        val mash_s = run_sh mash_ok mashN mash_facts goal
        val meng_mash_s = run_sh meng_mash_ok meng_mashN meng_mash_facts goal
        val dep_s = run_sh dep_ok depN deps_facts goal
      in
        ["Goal " ^ string_of_int j ^ ": " ^ name, meng_s, mash_s, meng_mash_s,
         dep_s]
        |> cat_lines |> tracing
      end
    val explode_suggs = space_explode " " #> filter_out (curry (op =) "")
    fun do_line (j, line) =
      case space_explode ":" line of
        [goal_name, suggs] => solve_goal j goal_name (explode_suggs suggs)
      | _ => ()
    fun total_of heading ok n =
      " " ^ heading ^ ": " ^ string_of_int (!ok) ^ " (" ^
      Real.fmt (StringCvt.FIX (SOME 1))
               (100.0 * Real.fromInt (!ok) / Real.fromInt n) ^ "%)"
    val inst_inducts = Config.get ctxt Sledgehammer_Filter.instantiate_inducts
    val options =
      [prover_name, string_of_int (the max_relevant) ^ " facts",
       "slice" |> not slice ? prefix "dont_", the_default "smart" type_enc,
       the_default "smart" lam_trans, ATP_Util.string_from_time timeout,
       "instantiate_inducts" |> not inst_inducts ? prefix "dont_"]
    val n = length lines
  in
    tracing " * * *";
    tracing ("Options: " ^ commas options);
    List.app do_line (tag_list 1 lines);
    ["Successes (of " ^ string_of_int n ^ " goals)",
     total_of mengN meng_ok n,
     total_of mashN mash_ok n,
     total_of meng_mashN meng_mash_ok n,
     total_of depN dep_ok n]
    |> cat_lines |> tracing
  end

end;
