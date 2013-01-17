(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type params = Sledgehammer_Provers.params

  val generate_accessibility :
    Proof.context -> theory list -> bool -> string -> unit
  val generate_features :
    Proof.context -> string -> theory list -> bool -> string -> unit
  val generate_isar_dependencies :
    Proof.context -> theory list -> bool -> string -> unit
  val generate_prover_dependencies :
    Proof.context -> params -> int * int option -> theory list -> bool -> string
    -> unit
  val generate_isar_commands :
    Proof.context -> string -> (int * int option) * int -> theory list -> string
    -> unit
  val generate_prover_commands :
    Proof.context -> params -> (int * int option) * int -> theory list -> string
    -> unit
  val generate_mepo_suggestions :
    Proof.context -> params -> (int * int option) * int -> theory list -> int
    -> string -> unit
  val generate_mesh_suggestions : int -> string -> string -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Fact
open Sledgehammer_MePo
open Sledgehammer_MaSh

fun in_range (from, to) j =
  j >= from andalso (to = NONE orelse j <= the to)

fun has_thm_thy th thy =
  Context.theory_name thy = Context.theory_name (theory_of_thm th)

fun has_thys thys th = exists (has_thm_thy th) thys

fun all_facts ctxt =
  let val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt in
    Sledgehammer_Fact.all_facts ctxt true false Symtab.empty [] [] css
    |> sort (thm_ord o pairself snd)
  end

fun generate_accessibility ctxt thys include_thys file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_fact fact prevs =
      let
        val s = encode_str fact ^ ": " ^ encode_strs prevs ^ "\n"
        val _ = File.append path s
      in [fact] end
    val facts =
      all_facts ctxt
      |> not include_thys ? filter_out (has_thys thys o snd)
      |> map (snd #> nickname_of_thm)
  in fold do_fact facts []; () end

fun generate_features ctxt prover thys include_thys file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_facts ctxt
      |> not include_thys ? filter_out (has_thys thys o snd)
    fun do_fact ((_, stature), th) =
      let
        val name = nickname_of_thm th
        val feats =
          features_of ctxt prover (theory_of_thm th) stature [prop_of th]
        val s =
          encode_str name ^ ": " ^ encode_features (sort_wrt fst feats) ^ "\n"
      in File.append path s end
  in List.app do_fact facts end

fun isar_or_prover_dependencies_of ctxt params_opt facts name_tabs th
                                   isar_deps_opt =
  case params_opt of
    SOME (params as {provers = prover :: _, ...}) =>
    prover_dependencies_of ctxt params prover 0 facts name_tabs th |> snd
  | NONE =>
    case isar_deps_opt of
      SOME deps => deps
    | NONE => isar_dependencies_of name_tabs th

fun generate_isar_or_prover_dependencies ctxt params_opt range thys include_thys
                                         file_name =
  let
    val path = file_name |> Path.explode
    val facts =
      all_facts ctxt |> not include_thys ? filter_out (has_thys thys o snd)
    val name_tabs = build_name_tables nickname_of_thm facts
    fun do_fact (j, (_, th)) =
      if in_range range j then
        let
          val name = nickname_of_thm th
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val deps =
            isar_or_prover_dependencies_of ctxt params_opt facts name_tabs th
                                           NONE
        in encode_str name ^ ": " ^ encode_strs deps ^ "\n" end
      else
        ""
    val lines = Par_List.map do_fact (tag_list 1 facts)
  in File.write_list path lines end

fun generate_isar_dependencies ctxt =
  generate_isar_or_prover_dependencies ctxt NONE (1, NONE)

fun generate_prover_dependencies ctxt params =
  generate_isar_or_prover_dependencies ctxt (SOME params)

fun is_bad_query ctxt ho_atp step j th isar_deps =
  j mod step <> 0 orelse
  Thm.legacy_get_kind th = "" orelse
  null (these (trim_dependencies th isar_deps)) orelse
  is_blacklisted_or_something ctxt ho_atp (Thm.get_name_hint th)

fun generate_isar_or_prover_commands ctxt prover params_opt (range, step) thys
                                     file_name =
  let
    val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover
    val path = file_name |> Path.explode
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val name_tabs = build_name_tables nickname_of_thm facts
    fun do_fact (j, ((name, ((_, stature), th)), prevs)) =
      if in_range range j then
        let
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val feats =
            features_of ctxt prover (theory_of_thm th) stature [prop_of th]
          val isar_deps = isar_dependencies_of name_tabs th
          val deps =
            isar_or_prover_dependencies_of ctxt params_opt facts name_tabs th
                                           (SOME isar_deps)
          val core =
            encode_str name ^ ": " ^ encode_strs prevs ^ "; " ^
            encode_features (sort_wrt fst feats)
          val query =
            if is_bad_query ctxt ho_atp step j th isar_deps then ""
            else "? " ^ core ^ "\n"
          val update =
            "! " ^ core ^ "; " ^
            encode_strs (these (trim_dependencies th deps)) ^ "\n"
        in query ^ update end
      else
        ""
    val parents =
      map (nickname_of_thm o snd) (the_list (try List.last old_facts))
    val new_facts = new_facts |> map (`(nickname_of_thm o snd))
    val prevss = fst (split_last (parents :: map (single o fst) new_facts))
    val lines = Par_List.map do_fact (tag_list 1 (new_facts ~~ prevss))
  in File.write_list path lines end

fun generate_isar_commands ctxt prover =
  generate_isar_or_prover_commands ctxt prover NONE

fun generate_prover_commands ctxt (params as {provers = prover :: _, ...}) =
  generate_isar_or_prover_commands ctxt prover (SOME params)

fun generate_mepo_suggestions ctxt (params as {provers = prover :: _, ...})
                              (range, step) thys max_suggs file_name =
  let
    val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover
    val path = file_name |> Path.explode
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val name_tabs = build_name_tables nickname_of_thm facts
    fun do_fact (j, ((_, th), old_facts)) =
      if in_range range j then
        let
          val name = nickname_of_thm th
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
          val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
          val isar_deps = isar_dependencies_of name_tabs th
        in
          if is_bad_query ctxt ho_atp step j th isar_deps then
            ""
          else
            let
              val suggs =
                old_facts
                |> Sledgehammer_MePo.mepo_suggested_facts ctxt params prover
                       max_suggs NONE hyp_ts concl_t
                |> map (nickname_of_thm o snd)
            in encode_str name ^ ": " ^ encode_strs suggs ^ "\n" end
        end
      else
        ""
    fun accum x (yss as ys :: _) = (x :: ys) :: yss
    val old_factss = tl (fold accum new_facts [old_facts])
    val lines = Par_List.map do_fact (tag_list 1 (new_facts ~~ rev old_factss))
  in File.write_list path lines end

fun generate_mesh_suggestions max_suggs mash_file_name mepo_file_name
                              mesh_file_name =
  let
    val mesh_path = Path.explode mesh_file_name
    val _ = File.write mesh_path ""
    fun do_fact (mash_line, mepo_line) =
      let
        val (name, mash_suggs) =
          extract_suggestions mash_line
          ||> weight_mash_facts
        val (name', mepo_suggs) =
          extract_suggestions mepo_line
          ||> weight_mepo_facts
        val _ = if name = name' then () else error "Input files out of sync."
        val mess =
          [(mepo_weight, (mepo_suggs, [])),
           (mash_weight, (mash_suggs, []))]
        val mesh_suggs = mesh_facts (op =) max_suggs mess
        val mesh_line = encode_str name ^ ": " ^ encode_strs mesh_suggs ^ "\n"
      in File.append mesh_path mesh_line end
    val mash_lines = Path.explode mash_file_name |> File.read_lines
    val mepo_lines = Path.explode mepo_file_name |> File.read_lines
  in
    if length mash_lines = length mepo_lines then
      List.app do_fact (mash_lines ~~ mepo_lines)
    else
      warning "Skipped: MaSh file missing or out of sync with MePo file."
  end

end;
