(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type params = Sledgehammer_Provers.params

  val generate_accessibility : theory -> bool -> string -> unit
  val generate_features : Proof.context -> theory -> bool -> string -> unit
  val generate_isa_dependencies : theory -> bool -> string -> unit
  val generate_atp_dependencies :
    Proof.context -> params -> theory -> bool -> string -> unit
  val generate_commands : Proof.context -> theory -> string -> unit
  val generate_iter_suggestions :
    Proof.context -> params -> theory -> int -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Fact
open Sledgehammer_Filter_Iter
open Sledgehammer_Filter_MaSh

fun thy_of_fact thy = Context.this_theory thy o thy_name_of_fact

fun generate_accessibility thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_fact fact prevs =
      let
        val s = escape_meta fact ^ ": " ^ escape_metas prevs ^ "\n"
        val _ = File.append path s
      in [fact] end
    val thy_facts =
      all_non_tautological_facts_of thy Termtab.empty
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> thy_facts_from_thms
    fun do_thy facts =
      let
        val thy = thy_of_fact thy (hd facts)
        val parents = parent_facts thy thy_facts
      in fold do_fact facts parents; () end
  in Symtab.fold (fn (_, facts) => K (do_thy facts)) thy_facts () end

fun generate_features ctxt thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val css_table = clasimpset_rule_table_of ctxt
    val facts =
      all_non_tautological_facts_of thy css_table
      |> not include_thy ? filter_out (has_thy thy o snd)
    fun do_fact ((_, (_, status)), th) =
      let
        val name = Thm.get_name_hint th
        val feats = features_of (theory_of_thm th) status [prop_of th]
        val s = escape_meta name ^ ": " ^ escape_metas feats ^ "\n"
      in File.append path s end
  in List.app do_fact facts end

fun generate_isa_dependencies thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val ths =
      all_non_tautological_facts_of thy Termtab.empty
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val deps = isabelle_dependencies_of all_names th
        val s = escape_meta name ^ ": " ^ escape_metas deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_atp_dependencies ctxt (params as {provers, max_facts, ...}) thy
                              include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_non_tautological_facts_of thy Termtab.empty
      |> not include_thy ? filter_out (has_thy thy o snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun is_dep dep (_, th) = Thm.get_name_hint th = dep
    fun add_isa_dep facts dep accum =
      if exists (is_dep dep) accum then
        accum
      else case find_first (is_dep dep) facts of
        SOME ((name, status), th) => accum @ [((name, status), th)]
      | NONE => accum (* shouldn't happen *)
    fun fix_name ((_, stature), th) =
      ((fn () => th |> Thm.get_name_hint, stature), th)
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val deps =
          case isabelle_dependencies_of all_names th of
            [] => []
          | isa_dep as [_] => isa_dep (* can hardly beat that *)
          | isa_deps =>
            let
              val facts =
                facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
              val facts =
                facts |> iterative_relevant_facts ctxt params (hd provers)
                             (the max_facts) NONE hyp_ts concl_t
                      |> fold (add_isa_dep facts) isa_deps
                      |> map fix_name
            in
              case run_prover ctxt params facts goal of
                {outcome = NONE, used_facts, ...} =>
                used_facts |> map fst |> sort string_ord
              | _ => isa_deps
            end
        val s = escape_meta name ^ ": " ^ escape_metas deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_commands ctxt thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val facts = all_non_tautological_facts_of thy css_table
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_fact ((_, (_, status)), th) prevs =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy status [prop_of th]
        val deps = isabelle_dependencies_of all_names th
        val kind = Thm.legacy_get_kind th
        val core = escape_metas prevs ^ "; " ^ escape_metas feats
        val query = if kind <> "" then "? " ^ core ^ "\n" else ""
        val update =
          "! " ^ escape_meta name ^ ": " ^ core ^ "; " ^
          escape_metas deps ^ "\n"
        val _ = File.append path (query ^ update)
      in [name] end
    val thy_facts = old_facts |> thy_facts_from_thms
    val parents = parent_facts thy thy_facts
  in fold do_fact new_facts parents; () end

fun generate_iter_suggestions ctxt (params as {provers, ...}) thy max_relevant
                              file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val facts = all_non_tautological_facts_of thy css_table
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    fun do_fact (fact as (_, th)) old_facts =
      let
        val name = Thm.get_name_hint th
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val kind = Thm.legacy_get_kind th
        val _ =
          if kind <> "" then
            let
              val suggs =
                old_facts
                |> Sledgehammer_Filter_Iter.iterative_relevant_facts ctxt params
                                (hd provers) max_relevant NONE hyp_ts concl_t
                |> map (fn ((name, _), _) => name ())
                |> sort string_ord
              val s = escape_meta name ^ ": " ^ escape_metas suggs ^ "\n"
            in File.append path s end
          else
            ()
      in fact :: old_facts end
  in fold do_fact new_facts old_facts; () end

end;
