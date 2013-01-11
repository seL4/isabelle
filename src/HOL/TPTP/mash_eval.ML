(*  Title:      HOL/TPTP/mash_eval.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Evaluate proof suggestions from MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EVAL =
sig
  type params = Sledgehammer_Provers.params

  val evaluate_mash_suggestions :
    Proof.context -> params -> int * int option -> string option -> string
    -> string -> unit
end;

structure MaSh_Eval : MASH_EVAL =
struct

open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_MePo
open Sledgehammer_MaSh
open Sledgehammer_Provers
open Sledgehammer_Isar

val MePoN = "MePo"
val MaShN = "MaSh"
val MeShN = "MeSh"
val IsarN = "Isar"

fun in_range (from, to) j =
  j >= from andalso (to = NONE orelse j <= the to)

fun evaluate_mash_suggestions ctxt params range prob_dir_name sugg_file_name
                              report_file_name =
  let
    val report_path = report_file_name |> Path.explode
    val _ = File.write report_path ""
    fun print s = File.append report_path (s ^ "\n")
    val {provers, max_facts, slice, type_enc, lam_trans, timeout, ...} =
      default_params ctxt []
    val prover = hd provers
    val slack_max_facts = generous_max_facts (the max_facts)
    val lines = Path.explode sugg_file_name |> File.read_lines
    val css = clasimpset_rule_table_of ctxt
    val facts = all_facts ctxt true false Symtab.empty [] [] css
    val name_tabs = build_name_tables nickname_of_thm facts
    fun with_index facts s = (find_index (curry (op =) s) facts + 1, s)
    fun index_string (j, s) = s ^ "@" ^ string_of_int j
    fun str_of_res label facts ({outcome, run_time, used_facts, ...}
                                : prover_result) =
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
      if in_range range j then
        let
          val (name, suggs) = extract_suggestions line
          val th =
            case find_first (fn (_, th) => nickname_of_thm th = name) facts of
              SOME (_, th) => th
            | NONE => error ("No fact called \"" ^ name ^ "\".")
          val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
          val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
          val isar_deps = isar_dependencies_of name_tabs th
          val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
          val mepo_facts =
            mepo_suggested_facts ctxt params prover slack_max_facts NONE hyp_ts
                concl_t facts
            |> weight_mepo_facts
          val (mash_facts, mash_unks) =
            find_mash_suggestions slack_max_facts suggs facts [] []
            |>> weight_mash_facts
          val mess =
            [(mepo_weight, (mepo_facts, [])),
             (mash_weight, (mash_facts, mash_unks))]
          val mesh_facts =
            mesh_facts (Thm.eq_thm o pairself snd) slack_max_facts mess
          val isar_facts =
            find_suggested_facts (map (rpair 1.0) isar_deps) facts
          (* adapted from "mirabelle_sledgehammer.ML" *)
          fun set_file_name heading (SOME dir) =
              let
                val prob_prefix =
                  "goal_" ^ string_of_int j ^ "__" ^ escape_meta name ^ "__" ^
                  heading
              in
                Config.put dest_dir dir
                #> Config.put problem_prefix (prob_prefix ^ "__")
                #> Config.put SMT_Config.debug_files (dir ^ "/" ^ prob_prefix)
              end
            | set_file_name _ NONE = I
          fun prove heading get facts =
            let
              fun nickify ((_, stature), th) =
                ((K (escape_meta (nickname_of_thm th)), stature), th)
              val facts =
                facts
                |> map (get #> nickify)
                |> maybe_instantiate_inducts ctxt hyp_ts concl_t
                |> take (the max_facts)
              val ctxt = ctxt |> set_file_name heading prob_dir_name
              val res as {outcome, ...} =
                run_prover_for_mash ctxt params prover facts goal
              val ok = if is_none outcome then 1 else 0
            in (str_of_res heading facts res, ok) end
          val ress =
            [fn () => prove MePoN fst mepo_facts,
             fn () => prove MaShN fst mash_facts,
             fn () => prove MeShN I mesh_facts,
             fn () => prove IsarN fst isar_facts]
            |> (* Par_List. *) map (fn f => f ())
        in
          "Goal " ^ string_of_int j ^ ": " ^ name :: map fst ress
          |> cat_lines |> print;
          map snd ress
        end
      else
        [0, 0, 0, 0]
    fun total_of heading ok n =
      "  " ^ heading ^ ": " ^ string_of_int ok ^ " (" ^
      Real.fmt (StringCvt.FIX (SOME 1))
               (100.0 * Real.fromInt ok / Real.fromInt n) ^ "%)"
    val inst_inducts = Config.get ctxt instantiate_inducts
    val options =
      ["prover = " ^ prover,
       "max_facts = " ^ string_of_int (the max_facts),
       "slice" |> not slice ? prefix "dont_",
       "type_enc = " ^ the_default "smart" type_enc,
       "lam_trans = " ^ the_default "smart" lam_trans,
       "timeout = " ^ ATP_Util.string_from_time (the_default one_year timeout),
       "instantiate_inducts" |> not inst_inducts ? prefix "dont_"]
    val _ = print " * * *";
    val _ = print ("Options: " ^ commas options);
    val oks = Par_List.map solve_goal (tag_list 1 lines)
    val n = length oks
    val [mepo_ok, mash_ok, mesh_ok, isar_ok] =
      map Integer.sum (map_transpose I oks)
  in
    ["Successes (of " ^ string_of_int n ^ " goals)",
     total_of MePoN mepo_ok n,
     total_of MaShN mash_ok n,
     total_of MeShN mesh_ok n,
     total_of IsarN isar_ok n]
    |> cat_lines |> print
  end

end;
