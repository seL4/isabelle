(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type params = Sledgehammer_Provers.params

  val generate_commands : theory -> string -> unit
  val generate_iter_suggestions :
    Proof.context -> params -> theory -> int -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Filter_MaSh

fun generate_commands thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = all_non_tautological_facts_of thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_fact ((_, (_, status)), th) prevs =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy (status, th)
        val deps = isabelle_dependencies_of all_names th
        val kind = Thm.legacy_get_kind th
        val name = fact_name_of name
        val core =
          name ^ ": " ^ space_implode " " prevs ^ "; " ^ space_implode " " feats
        val query = if kind <> "" then "? " ^ core ^ "\n" else ""
        val update = "! " ^ core ^ "; " ^ space_implode " " deps ^ "\n"
        val _ = File.append path (query ^ update)
      in [name] end
    val thy_ths = old_facts |> thms_by_thy
    val parents = parent_thms thy_ths thy
  in fold do_fact new_facts parents; () end

fun generate_iter_suggestions ctxt (params as {provers, ...}) thy max_relevant
                              file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = all_non_tautological_facts_of thy
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
                |> map (fn ((name, _), _) => fact_name_of (name ()))
                |> sort string_ord
              val s = fact_name_of name ^ ": " ^ space_implode " " suggs ^ "\n"
            in File.append path s end
          else
            ()
      in fact :: old_facts end
  in fold do_fact new_facts old_facts; () end

end;
