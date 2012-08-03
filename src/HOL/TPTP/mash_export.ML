(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type params = Sledgehammer_Provers.params

  val generate_accessibility : Proof.context -> theory -> bool -> string -> unit
  val generate_features :
    Proof.context -> string -> theory -> bool -> string -> unit
  val generate_isar_dependencies :
    Proof.context -> theory -> bool -> string -> unit
  val generate_atp_dependencies :
    Proof.context -> params -> theory -> bool -> string -> unit
  val generate_commands : Proof.context -> params -> theory -> string -> unit
  val generate_mepo_suggestions :
    Proof.context -> params -> theory -> int -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Fact
open Sledgehammer_MePo
open Sledgehammer_MaSh

fun thy_map_from_facts ths =
  ths |> sort (thm_ord o swap o pairself snd)
      |> map (snd #> `(theory_of_thm #> Context.theory_name))
      |> AList.coalesce (op =)
      |> map (apsnd (map nickname_of))

fun has_thy thy th =
  Context.theory_name thy = Context.theory_name (theory_of_thm th)

fun all_non_technical_facts ctxt thy =
  let val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt in
    all_facts (Proof_Context.init_global thy) false Symtab.empty [] [] css
    |> filter_out (is_thm_technical o snd)
  end

fun parent_facts thy thy_map =
  let
    fun add_last thy =
      case AList.lookup (op =) thy_map (Context.theory_name thy) of
        SOME (last_fact :: _) => insert (op =) last_fact
      | _ => add_parent thy
    and add_parent thy = fold add_last (Theory.parents_of thy)
  in add_parent thy [] end

val thy_name_of_fact = hd o Long_Name.explode
fun thy_of_fact thy = Context.this_theory thy o thy_name_of_fact

val all_names = map (rpair () o nickname_of) #> Symtab.make

fun generate_accessibility ctxt thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_fact fact prevs =
      let
        val s = escape_meta fact ^ ": " ^ escape_metas prevs ^ "\n"
        val _ = File.append path s
      in [fact] end
    val thy_map =
      all_non_technical_facts ctxt thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> thy_map_from_facts
    fun do_thy facts =
      let
        val thy = thy_of_fact thy (hd facts)
        val parents = parent_facts thy thy_map
      in fold_rev do_fact facts parents; () end
  in fold_rev (fn (_, facts) => fn () => do_thy facts) thy_map () end

fun generate_features ctxt prover thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_non_technical_facts ctxt thy
      |> not include_thy ? filter_out (has_thy thy o snd)
    fun do_fact ((_, stature), th) =
      let
        val name = nickname_of th
        val feats =
          features_of ctxt prover (theory_of_thm th) stature [prop_of th]
        val s = escape_meta name ^ ": " ^ escape_metas feats ^ "\n"
      in File.append path s end
  in List.app do_fact facts end

fun generate_isar_dependencies ctxt thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val ths =
      all_non_technical_facts ctxt thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> map snd
    val all_names = all_names ths
    fun do_thm th =
      let
        val name = nickname_of th
        val deps = isar_dependencies_of all_names th |> these
        val s = escape_meta name ^ ": " ^ escape_metas deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_atp_dependencies ctxt (params as {provers, ...}) thy include_thy
                              file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val prover = hd provers
    val facts =
      all_non_technical_facts ctxt thy
      |> not include_thy ? filter_out (has_thy thy o snd)
    val ths = facts |> map snd
    val all_names = all_names ths
    fun do_thm th =
      let
        val name = nickname_of th
        val deps =
          atp_dependencies_of ctxt params prover 0 facts all_names th
          |> snd |> these
        val s = escape_meta name ^ ": " ^ escape_metas deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_commands ctxt (params as {provers, ...}) thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val prover = hd provers
    val facts = all_non_technical_facts ctxt thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    val all_names = all_names (map snd facts)
    fun do_fact ((_, stature), th) prevs =
      let
        val name = nickname_of th
        val feats = features_of ctxt prover thy stature [prop_of th]
        val deps =
          atp_dependencies_of ctxt params prover 0 facts all_names th
          |> snd |> these
        val kind = Thm.legacy_get_kind th
        val core =
          escape_meta name ^ ": " ^ escape_metas prevs ^ "; " ^
          escape_metas feats
        val query = if kind <> "" then "? " ^ core ^ "\n" else ""
        val update = "! " ^ core ^ "; " ^ escape_metas deps ^ "\n"
        val _ = File.append path (query ^ update)
      in [name] end
    val thy_map = old_facts |> thy_map_from_facts
    val parents = parent_facts thy thy_map
  in fold do_fact new_facts parents; () end

fun generate_mepo_suggestions ctxt (params as {provers, ...}) thy max_relevant
                              file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val prover = hd provers
    val facts = all_non_technical_facts ctxt thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    fun do_fact (fact as (_, th)) old_facts =
      let
        val name = nickname_of th
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val kind = Thm.legacy_get_kind th
        val _ =
          if kind <> "" then
            let
              val suggs =
                old_facts
                |> Sledgehammer_MePo.mepo_suggested_facts ctxt params prover
                       max_relevant NONE hyp_ts concl_t
                |> map (fn ((name, _), _) => name ())
              val s = escape_meta name ^ ": " ^ escape_metas suggs ^ "\n"
            in File.append path s end
          else
            ()
      in fact :: old_facts end
  in fold do_fact new_facts old_facts; () end

end;
