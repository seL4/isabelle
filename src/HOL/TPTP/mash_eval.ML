(*  Title:      HOL/TPTP/mash_eval.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Evaluate proof suggestions from MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EVAL =
sig
  type params = Sledgehammer_Prover.params

  val evaluate_mash_suggestions : Proof.context -> params -> int * int option -> string option ->
    string list -> string -> unit
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
open MaSh_Export

val prefix = Library.prefix

fun evaluate_mash_suggestions ctxt params range prob_dir_name file_names report_file_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val zeros = [0, 0, 0, 0, 0, 0]
    val report_path = report_file_name |> Path.explode
    val _ = File.write report_path ""

    fun print s = File.append report_path (s ^ "\n")

    val {provers, max_facts, slice, type_enc, lam_trans, timeout, induction_rules, ...} =
      default_params thy []
    val prover = hd provers
    val max_suggs = generous_max_suggestions (the max_facts)
    val inst_inducts = induction_rules = SOME Instantiate

    val method_of_file_name =
      perhaps (try (unsuffix "_suggestions")) o List.last o space_explode "/"

    val methods = "isar" :: map method_of_file_name file_names
    val lines_of = Path.explode #> try File.read_lines #> these
    val liness0 = map lines_of file_names
    val num_lines = fold (Integer.max o length) liness0 0

    fun pad lines = lines @ replicate (num_lines - length lines) ""

    val liness' = Ctr_Sugar_Util.transpose (map pad liness0)

    val css = clasimpset_rule_table_of ctxt
    val facts = all_facts ctxt true Keyword.empty_keywords [] [] css
    val name_tabs = build_name_tables nickname_of_thm facts

    fun with_index facts s = (find_index (curry (op =) s) facts + 1, s)
    fun index_str (j, s) = s ^ "@" ^ string_of_int j
    val str_of_method = enclose "  " ": "

    fun str_of_result method facts ({outcome, run_time, used_facts, ...} : prover_result) =
      let val facts = facts |> map (fst o fst) in
        str_of_method method ^
        (if is_none outcome then
           "Success (" ^ ATP_Util.string_of_time run_time ^ "): " ^
           (used_facts |> map (with_index facts o fst)
                       |> sort (int_ord o apply2 fst)
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

    fun solve_goal (j, lines) =
      if in_range range j andalso exists (curry (op <>) "") lines then
        let
          val get_suggs = extract_suggestions ##> (take max_suggs #> map fst)
          val (names, suggss0) = split_list (map get_suggs lines)
          val name =
            (case names |> filter (curry (op <>) "") |> distinct (op =) of
              [name] => name
            | names => error ("Input files out of sync: facts " ^ commas (map quote names)))
          val th =
            case find_first (fn (_, th) => nickname_of_thm th = name) facts of
              SOME (_, th) => th
            | NONE => error ("No fact called \"" ^ name)
          val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
          val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal 1 ctxt
          val isar_deps = these (isar_dependencies_of name_tabs th)
          val suggss = isar_deps :: suggss0
          val facts = facts |> filter (fn (_, th') => thm_less (th', th))

          (* adapted from "mirabelle_sledgehammer.ML" *)
          fun set_file_name method (SOME dir) =
              let
                val prob_prefix = "goal_" ^ string_of_int j ^ "__" ^ encode_str name ^ "__" ^ method
              in
                Config.put atp_dest_dir dir
                #> Config.put atp_problem_prefix (prob_prefix ^ "__")
                #> Config.put SMT_Config.debug_files (dir ^ "/" ^ prob_prefix)
              end
            | set_file_name _ NONE = I

          fun prove method suggs =
            if null facts then
              (str_of_method method ^ "Skipped", 0)
            else
              let
                fun nickify ((_, stature), th) =
                  ((K (encode_str (nickname_of_thm th)), stature), th)

                val facts =
                  suggs
                  |> find_suggested_facts ctxt facts
                  |> map (fact_of_raw_fact #> nickify)
                  |> inst_inducts ? instantiate_inducts ctxt hyp_ts concl_t
                  |> take (the max_facts)
                  |> map fact_of_raw_fact
                val ctxt = ctxt |> set_file_name method prob_dir_name
                val res as {outcome, ...} = run_prover_for_mash ctxt params prover name facts goal
                val ok = if is_none outcome then 1 else 0
              in
                (str_of_result method facts res, ok)
              end

          val ress = map2 prove methods suggss
        in
          "Goal " ^ string_of_int j ^ ": " ^ name :: map fst ress
          |> cat_lines |> print;
          map snd ress
        end
      else
        zeros

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
    val oks = Par_List.map solve_goal (tag_list 1 liness')
    val n = length oks

    fun total_of method ok =
      str_of_method method ^ string_of_int ok ^ " (" ^ Real.fmt (StringCvt.FIX (SOME 1))
        (100.0 * Real.fromInt ok / Real.fromInt (Int.max (1, n))) ^ "%)"

    val oks' = if n = 0 then zeros else map Integer.sum (map_transpose I oks)
  in
    "Successes (of " ^ string_of_int n ^ " goals)" ::
    map2 total_of methods oks'
    |> cat_lines |> print
  end

end;
