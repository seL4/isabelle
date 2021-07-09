(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type params = Sledgehammer_Prover.params

  val in_range : int * int option -> int -> bool
  val extract_suggestions : string -> string * (string * real) list

  val generate_accessibility : Proof.context -> theory list -> string -> unit
  val generate_features : Proof.context -> theory list -> string -> unit
  val generate_isar_dependencies : Proof.context -> int * int option -> theory list -> string ->
    unit
  val generate_prover_dependencies : Proof.context -> params -> int * int option -> theory list ->
    string -> unit
  val generate_isar_commands : Proof.context -> string -> (int * int option) * int -> theory list ->
    int -> string -> unit
  val generate_prover_commands : Proof.context -> params -> (int * int option) * int ->
    theory list -> int -> string -> unit
  val generate_mepo_suggestions : Proof.context -> params -> (int * int option) * int ->
    theory list -> int -> string -> unit
  val generate_mash_suggestions : string -> Proof.context -> params -> (int * int option) * int ->
    theory list -> int -> string -> unit
  val generate_mesh_suggestions : int -> string -> string -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Fact
open Sledgehammer_Prover_ATP
open Sledgehammer_MePo
open Sledgehammer_MaSh

fun in_range (from, to) j =
  j >= from andalso (to = NONE orelse j <= the to)

fun encode_feature (names, weight) =
  encode_str names ^ (if Real.== (weight, 1.0) then "" else "=" ^ Real.toString weight)

val encode_features = map encode_feature #> space_implode " "

(* The suggested weights do not make much sense. *)
fun extract_suggestion sugg =
  (case space_explode "=" sugg of
    [name, weight] => SOME (decode_str name, Real.fromString weight |> the_default 1.0)
  | [name] => SOME (decode_str name, 1.0)
  | _ => NONE)

fun extract_suggestions line =
  (case space_explode ":" line of
    [goal, suggs] => (decode_str goal, map_filter extract_suggestion (space_explode " " suggs))
  | _ => ("", []))

fun has_thm_thy th thy =
  Context.theory_name thy = Thm.theory_name th

fun has_thys thys th = exists (has_thm_thy th) thys

fun all_facts ctxt =
  let val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt in
    Sledgehammer_Fact.all_facts ctxt true Keyword.empty_keywords [] [] css
    |> sort (crude_thm_ord ctxt o apply2 snd)
  end

fun filter_accessible_from th = filter (fn (_, th') => thm_less (th', th))

fun generate_accessibility ctxt thys file_name =
  let
    val path = Path.explode file_name

    fun do_fact (parents, fact) =
      let val s = encode_str fact ^ ": " ^ encode_strs parents ^ "\n" in
        File.append path s
      end

    val facts =
      all_facts ctxt
      |> filter_out (has_thys thys o snd)
      |> attach_parents_to_facts []
      |> map (apsnd (nickname_of_thm o snd))
  in
    File.write path "";
    List.app do_fact facts
  end

fun generate_features ctxt thys file_name =
  let
    val path = Path.explode file_name
    val _ = File.write path ""
    val facts = all_facts ctxt |> filter_out (has_thys thys o snd)

    fun do_fact ((_, stature), th) =
      let
        val name = nickname_of_thm th
        val feats = features_of ctxt (Thm.theory_name th) stature [Thm.prop_of th]
        val s = encode_str name ^ ": " ^ encode_strs (sort string_ord feats) ^ "\n"
      in
        File.append path s
      end
  in
    List.app do_fact facts
  end

val prover_marker = "$a"
val isar_marker = "$i"
val omitted_marker = "$o"
val unprovable_marker = "$u" (* axiom or definition or characteristic theorem *)
val prover_failed_marker = "$x"

fun smart_dependencies_of ctxt params_opt facts name_tabs th isar_deps_opt =
  let
    val (marker, deps) =
      (case params_opt of
        SOME (params as {provers = prover :: _, ...}) =>
        prover_dependencies_of ctxt params prover 0 facts name_tabs th
        |>> (fn true => prover_marker | false => prover_failed_marker)
      | NONE =>
        let
          val deps =
            (case isar_deps_opt of
              NONE => isar_dependencies_of name_tabs th
            | deps => deps)
        in
          (case deps of
            NONE => (omitted_marker, [])
          | SOME [] => (unprovable_marker, [])
          | SOME deps => (isar_marker, deps))
        end)
  in
    (case trim_dependencies deps of
      SOME deps => (marker, deps)
    | NONE => (omitted_marker, []))
  end

fun generate_isar_or_prover_dependencies ctxt params_opt range thys file_name =
  let
    val path = Path.explode file_name
    val facts = filter_out (has_thys thys o snd) (all_facts ctxt)
    val name_tabs = build_name_tables nickname_of_thm facts

    fun do_fact (j, (_, th)) =
      if in_range range j then
        let
          val name = nickname_of_thm th
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val access_facts = filter_accessible_from th facts
          val (marker, deps) = smart_dependencies_of ctxt params_opt access_facts name_tabs th NONE
        in
          encode_str name ^ ": " ^ marker ^ " " ^ encode_strs deps ^ "\n"
        end
      else
        ""

    val lines = map do_fact (tag_list 1 facts)
  in
    File.write_list path lines
  end

fun generate_isar_dependencies ctxt =
  generate_isar_or_prover_dependencies ctxt NONE

fun generate_prover_dependencies ctxt params =
  generate_isar_or_prover_dependencies ctxt (SOME params)

fun is_bad_query ctxt ho_atp step j th isar_deps =
  j mod step <> 0 orelse
  Thm.legacy_get_kind th = "" orelse
  null (the_list isar_deps) orelse
  is_blacklisted_or_something (Thm.get_name_hint th)

fun generate_isar_or_prover_commands ctxt prover params_opt (range, step) thys max_suggs file_name =
  let
    val ho_atp = is_ho_atp ctxt prover
    val path = Path.explode file_name
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val name_tabs = build_name_tables nickname_of_thm facts

    fun do_fact (j, (name, (parents, ((_, stature), th)))) =
      if in_range range j then
        let
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val isar_deps = isar_dependencies_of name_tabs th
          val do_query = not (is_bad_query ctxt ho_atp step j th isar_deps)
          val goal_feats = features_of ctxt (Thm.theory_name th) stature [Thm.prop_of th]
          val access_facts = filter_accessible_from th new_facts @ old_facts
          val (marker, deps) =
            smart_dependencies_of ctxt params_opt access_facts name_tabs th isar_deps

          fun extra_features_of (((_, stature), th), weight) =
            [Thm.prop_of th]
            |> features_of ctxt (Thm.theory_name th) stature
            |> map (rpair (weight * extra_feature_factor))

          val query =
            if do_query then
              let
                val query_feats =
                  new_facts
                  |> drop (j - num_extra_feature_facts)
                  |> take num_extra_feature_facts
                  |> rev
                  |> weight_facts_steeply
                  |> map extra_features_of
                  |> rpair (map (rpair 1.0) goal_feats)
                  |-> fold (union (eq_fst (op =)))
              in
                "? " ^ string_of_int max_suggs ^ " # " ^ encode_str name ^ ": " ^
                encode_strs parents ^ "; " ^ encode_features query_feats ^ "\n"
              end
            else
              ""
          val update =
            "! " ^ encode_str name ^ ": " ^ encode_strs parents ^ "; " ^ encode_strs goal_feats ^
            "; " ^ marker ^ " " ^ encode_strs deps ^ "\n"
        in query ^ update end
      else
        ""

    val new_facts =
      new_facts
      |> attach_parents_to_facts old_facts
      |> map (`(nickname_of_thm o snd o snd))
    val lines = map do_fact (tag_list 1 new_facts)
  in
    File.write_list path lines
  end

fun generate_isar_commands ctxt prover =
  generate_isar_or_prover_commands ctxt prover NONE

fun generate_prover_commands ctxt (params as {provers = prover :: _, ...}) =
  generate_isar_or_prover_commands ctxt prover (SOME params)

fun generate_mepo_or_mash_suggestions mepo_or_mash_suggested_facts ctxt
    (params as {provers = prover :: _, ...}) (range, step) thys max_suggs file_name =
  let
    val ho_atp = is_ho_atp ctxt prover
    val path = Path.explode file_name
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val name_tabs = build_name_tables nickname_of_thm facts

    fun do_fact (j, ((_, th), old_facts)) =
      if in_range range j then
        let
          val name = nickname_of_thm th
          val _ = tracing ("Fact " ^ string_of_int j ^ ": " ^ name)
          val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
          val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal 1 ctxt
          val isar_deps = isar_dependencies_of name_tabs th
        in
          if is_bad_query ctxt ho_atp step j th isar_deps then
            ""
          else
            let
              val suggs =
                old_facts
                |> filter_accessible_from th
                |> mepo_or_mash_suggested_facts ctxt (Thm.theory_name th)
                  params max_suggs hyp_ts concl_t
                |> map (nickname_of_thm o snd)
            in
              encode_str name ^ ": " ^ encode_strs suggs ^ "\n"
            end
        end
      else
        ""

    fun accum x (yss as ys :: _) = (x :: ys) :: yss
    val old_factss = tl (fold accum new_facts [rev old_facts])
    val lines = map do_fact (tag_list 1 (new_facts ~~ rev (map rev old_factss)))
  in
    File.write_list path lines
  end

val generate_mepo_suggestions =
  generate_mepo_or_mash_suggestions
    (fn ctxt => fn _ => fn params => fn max_suggs => fn hyp_ts => fn concl_t =>
       not (Config.get ctxt Sledgehammer_MaSh.duplicates) ? Sledgehammer_Fact.drop_duplicate_facts
       #> Sledgehammer_MePo.mepo_suggested_facts ctxt params max_suggs NONE hyp_ts concl_t)

fun generate_mash_suggestions algorithm ctxt =
  (Options.put_default \<^system_option>\<open>MaSh\<close> algorithm;
   Sledgehammer_MaSh.mash_unlearn ctxt;
   generate_mepo_or_mash_suggestions
     (fn ctxt => fn thy_name => fn params as {provers = prover :: _, ...} =>
          fn max_suggs => fn hyp_ts => fn concl_t =>
        tap (Sledgehammer_MaSh.mash_learn_facts ctxt params prover 2 false
          Sledgehammer_Util.one_year)
        #> Sledgehammer_MaSh.mash_suggested_facts ctxt thy_name params max_suggs hyp_ts concl_t
        #> fst) ctxt)

fun generate_mesh_suggestions max_suggs mash_file_name mepo_file_name mesh_file_name =
  let
    val mesh_path = Path.explode mesh_file_name
    val _ = File.write mesh_path ""

    fun do_fact (mash_line, mepo_line) =
      let
        val (name, mash_suggs) =
          extract_suggestions mash_line
          ||> (map fst #> weight_facts_steeply)
        val (name', mepo_suggs) =
          extract_suggestions mepo_line
          ||> (map fst #> weight_facts_steeply)
        val _ = if name = name' then () else error "Input files out of sync"
        val mess =
          [(mepo_weight, (mepo_suggs, [])),
           (mash_weight, (mash_suggs, []))]
        val mesh_suggs = mesh_facts I (op =) max_suggs mess
        val mesh_line = encode_str name ^ ": " ^ encode_strs mesh_suggs ^ "\n"
      in File.append mesh_path mesh_line end

    val mash_lines = Path.explode mash_file_name |> File.read_lines
    val mepo_lines = Path.explode mepo_file_name |> File.read_lines
  in
    if length mash_lines = length mepo_lines then List.app do_fact (mash_lines ~~ mepo_lines)
    else warning "Skipped: MaSh file missing or out of sync with MePo file"
  end

end;
