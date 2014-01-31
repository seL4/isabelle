(*  Title:      HOL/TPTP/mash_eval.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Evaluate proof suggestions from MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EVAL =
sig
  type params = Sledgehammer_Prover.params

  val MePoN : string
  val MaSh_IsarN : string
  val MaSh_ProverN : string
  val MeSh_IsarN : string
  val MeSh_ProverN : string
  val IsarN : string
  val evaluate_mash_suggestions :
    Proof.context -> params -> int * int option -> bool -> string list
    -> string option -> string -> string -> string -> string -> string -> string
    -> unit
end;

structure MaSh_Eval : MASH_EVAL =
struct

open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_MePo
open Sledgehammer_MaSh
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Commands

val prefix = Library.prefix

val MaSh_IsarN = MaShN ^ "-Isar"
val MaSh_ProverN = MaShN ^ "-Prover"
val MeSh_IsarN = MeShN ^ "-Isar"
val MeSh_ProverN = MeShN ^ "-Prover"
val IsarN = "Isar"

fun in_range (from, to) j =
  j >= from andalso (to = NONE orelse j <= the to)

fun evaluate_mash_suggestions ctxt params range linearize methods prob_dir_name
        mepo_file_name mash_isar_file_name mash_prover_file_name
        mesh_isar_file_name mesh_prover_file_name report_file_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val zeros = [0, 0, 0, 0, 0, 0]
    val report_path = report_file_name |> Path.explode
    val _ = File.write report_path ""
    fun print s = File.append report_path (s ^ "\n")
    val {provers, max_facts, slice, type_enc, lam_trans, timeout, ...} = default_params thy []
    val prover = hd provers
    val slack_max_facts = generous_max_facts (the max_facts)
    val lines_of = Path.explode #> try File.read_lines #> these
    val file_names =
      [mepo_file_name, mash_isar_file_name, mash_prover_file_name,
       mesh_isar_file_name, mesh_prover_file_name]
    val lines as [mepo_lines, mash_isar_lines, mash_prover_lines,
                  mesh_isar_lines, mesh_prover_lines] =
      map lines_of file_names
    val num_lines = fold (Integer.max o length) lines 0
    fun pad lines = lines @ replicate (num_lines - length lines) ""
    val lines =
      pad mepo_lines ~~ pad mash_isar_lines ~~ pad mash_prover_lines ~~
      pad mesh_isar_lines ~~ pad mesh_prover_lines
    val css = clasimpset_rule_table_of ctxt
    val facts = all_facts ctxt true false Symtab.empty [] [] css
    val name_tabs = build_name_tables nickname_of_thm facts
    fun with_index facts s = (find_index (curry (op =) s) facts + 1, s)
    fun index_str (j, s) = s ^ "@" ^ string_of_int j
    val str_of_method = enclose "  " ": "
    fun str_of_result method facts ({outcome, run_time, used_facts, ...}
                                     : prover_result) =
      let val facts = facts |> map (fst o fst) in
        str_of_method method ^
        (if is_none outcome then
           "Success (" ^ ATP_Util.string_of_time run_time ^ "): " ^
           (used_facts |> map (with_index facts o fst)
                       |> sort (int_ord o pairself fst)
                       |> map index_str
                       |> space_implode " ") ^
           (if length facts < the max_facts then
              " (of " ^ string_of_int (length facts) ^ ")"
            else
              "")
         else
           "Failure: " ^
           (facts |> take (the max_facts) |> tag_list 1
                  |> map index_str
                  |> space_implode " "))
      end
    fun solve_goal (j, ((((mepo_line, mash_isar_line), mash_prover_line),
                         mesh_isar_line), mesh_prover_line)) =
      if in_range range j then
        let
          val get_suggs = extract_suggestions ##> take slack_max_facts
          val (name1, mepo_suggs) = get_suggs mepo_line
          val (name2, mash_isar_suggs) = get_suggs mash_isar_line
          val (name3, mash_prover_suggs) = get_suggs mash_prover_line
          val (name4, mesh_isar_suggs) = get_suggs mesh_isar_line
          val (name5, mesh_prover_suggs) = get_suggs mesh_prover_line
          val [name] =
            [name1, name2, name3, name4, name5]
            |> filter (curry (op <>) "") |> distinct (op =)
            handle General.Match => error "Input files out of sync."
          val th =
            case find_first (fn (_, th) => nickname_of_thm th = name) facts of
              SOME (_, th) => th
            | NONE => error ("No fact called \"" ^ name ^ "\".")
          val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
          val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal 1 ctxt
          val isar_deps = isar_dependencies_of name_tabs th
          val facts =
            facts
            |> filter (fn (_, th') =>
                          if linearize then crude_thm_ord (th', th) = LESS
                          else thm_less (th', th))
          (* adapted from "mirabelle_sledgehammer.ML" *)
          fun set_file_name method (SOME dir) =
              let
                val prob_prefix =
                  "goal_" ^ string_of_int j ^ "__" ^ encode_str name ^ "__" ^
                  method
              in
                Config.put atp_dest_dir dir
                #> Config.put atp_problem_prefix (prob_prefix ^ "__")
                #> Config.put SMT_Config.debug_files (dir ^ "/" ^ prob_prefix)
              end
            | set_file_name _ NONE = I
          fun prove method suggs =
            if not (member (op =) methods method) orelse
               (null facts andalso method <> IsarN) then
              (str_of_method method ^ "Skipped", 0)
            else
              let
                fun nickify ((_, stature), th) =
                  ((K (encode_str (nickname_of_thm th)), stature), th)
                val facts =
                  suggs
                  |> find_suggested_facts ctxt facts
                  |> map (fact_of_raw_fact #> nickify)
                  |> maybe_instantiate_inducts ctxt hyp_ts concl_t
                  |> take (the max_facts)
                  |> map fact_of_raw_fact
                val ctxt = ctxt |> set_file_name method prob_dir_name
                val res as {outcome, ...} =
                  run_prover_for_mash ctxt params prover name facts goal
                val ok = if is_none outcome then 1 else 0
              in (str_of_result method facts res, ok) end
          val ress =
            [fn () => prove MePoN mepo_suggs,
             fn () => prove MaSh_IsarN mash_isar_suggs,
             fn () => prove MaSh_ProverN mash_prover_suggs,
             fn () => prove MeSh_IsarN mesh_isar_suggs,
             fn () => prove MeSh_ProverN mesh_prover_suggs,
             fn () => prove IsarN isar_deps]
            |> (* Par_List. *) map (fn f => f ())
        in
          "Goal " ^ string_of_int j ^ ": " ^ name :: map fst ress
          |> cat_lines |> print;
          map snd ress
        end
      else
        zeros
    fun total_of method ok n =
      str_of_method method ^ string_of_int ok ^ " (" ^
      Real.fmt (StringCvt.FIX (SOME 1))
               (100.0 * Real.fromInt ok / Real.fromInt (Int.max (1, n))) ^ "%)"
    val inst_inducts = Config.get ctxt instantiate_inducts
    val options =
      ["prover = " ^ prover,
       "max_facts = " ^ string_of_int (the max_facts),
       "slice" |> not slice ? prefix "dont_",
       "type_enc = " ^ the_default "smart" type_enc,
       "lam_trans = " ^ the_default "smart" lam_trans,
       "timeout = " ^ ATP_Util.string_of_time timeout,
       "instantiate_inducts" |> not inst_inducts ? prefix "dont_"]
    val _ = print " * * *";
    val _ = print ("Options: " ^ commas options);
    val oks = Par_List.map solve_goal (tag_list 1 lines)
    val n = length oks
    val [mepo_ok, mash_isar_ok, mash_prover_ok, mesh_isar_ok, mesh_prover_ok,
         isar_ok] =
      if n = 0 then zeros else map Integer.sum (map_transpose I oks)
  in
    ["Successes (of " ^ string_of_int n ^ " goals)",
     total_of MePoN mepo_ok n,
     total_of MaSh_IsarN mash_isar_ok n,
     total_of MaSh_ProverN mash_prover_ok n,
     total_of MeSh_IsarN mesh_isar_ok n,
     total_of MeSh_ProverN mesh_prover_ok n,
     total_of IsarN isar_ok n]
    |> cat_lines |> print
  end

end;
