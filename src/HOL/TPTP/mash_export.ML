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
    Proof.context -> params -> theory list -> bool -> string -> unit
  val generate_isar_commands :
    Proof.context -> string -> theory list -> string -> unit
  val generate_prover_commands :
    Proof.context -> params -> theory list -> string -> unit
  val generate_mepo_suggestions :
    Proof.context -> params -> theory list -> int -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open Sledgehammer_Fact
open Sledgehammer_MePo
open Sledgehammer_MaSh

fun thy_map_from_facts ths =
  ths |> rev
      |> map (snd #> `(theory_of_thm #> Context.theory_name))
      |> AList.coalesce (op =)
      |> map (apsnd (map nickname_of))

fun has_thm_thy th thy =
  Context.theory_name thy = Context.theory_name (theory_of_thm th)

fun has_thys thys th = exists (has_thm_thy th) thys

fun all_facts ctxt =
  let val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt in
    Sledgehammer_Fact.all_facts ctxt true false Symtab.empty [] [] css
    |> sort (thm_ord o pairself snd)
  end

fun add_thy_parent_facts thy_map thy =
  let
    fun add_last thy =
      case AList.lookup (op =) thy_map (Context.theory_name thy) of
        SOME (last_fact :: _) => insert (op =) last_fact
      | _ => add_parent thy
    and add_parent thy = fold add_last (Theory.parents_of thy)
  in add_parent thy end

val thy_name_of_fact = hd o Long_Name.explode
fun thy_of_fact thy = Context.get_theory thy o thy_name_of_fact

fun generate_accessibility ctxt thys include_thys file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_fact fact prevs =
      let
        val s = escape_meta fact ^ ": " ^ escape_metas prevs ^ "\n"
        val _ = File.append path s
      in [fact] end
    val thy_map =
      all_facts ctxt
      |> not include_thys ? filter_out (has_thys thys o snd)
      |> thy_map_from_facts
    fun do_thy facts =
      let
        val thy = thy_of_fact (Proof_Context.theory_of ctxt) (hd facts)
        val parents = add_thy_parent_facts thy_map thy []
      in fold_rev do_fact facts parents; () end
  in fold_rev (fn (_, facts) => fn () => do_thy facts) thy_map () end

fun generate_features ctxt prover thys include_thys file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_facts ctxt
      |> not include_thys ? filter_out (has_thys thys o snd)
    fun do_fact ((_, stature), th) =
      let
        val name = nickname_of th
        val feats =
          features_of ctxt prover (theory_of_thm th) stature [prop_of th]
        val s = escape_meta name ^ ": " ^ encode_features feats ^ "\n"
      in File.append path s end
  in List.app do_fact facts end

fun isar_or_prover_dependencies_of ctxt params_opt facts all_names th
                                   isar_deps_opt =
  (case params_opt of
     SOME (params as {provers = prover :: _, ...}) =>
     prover_dependencies_of ctxt params prover 0 facts all_names th |> snd
   | NONE =>
     case isar_deps_opt of
       SOME deps => deps
     | NONE => isar_dependencies_of all_names th)
  |> these

fun generate_isar_or_prover_dependencies ctxt params_opt thys include_thys
                                         file_name =
  let
    val path = file_name |> Path.explode
    val facts =
      all_facts ctxt |> not include_thys ? filter_out (has_thys thys o snd)
    val all_names = build_all_names nickname_of facts
    fun do_fact (_, th) =
      let
        val name = nickname_of th
        val deps =
          isar_or_prover_dependencies_of ctxt params_opt facts all_names th NONE
      in escape_meta name ^ ": " ^ escape_metas deps ^ "\n" end
    val lines = Par_List.map do_fact facts
  in File.write_list path lines end

fun generate_isar_dependencies ctxt =
  generate_isar_or_prover_dependencies ctxt NONE

fun generate_prover_dependencies ctxt params =
  generate_isar_or_prover_dependencies ctxt (SOME params)

fun is_bad_query ctxt ho_atp th isar_deps =
  Thm.legacy_get_kind th = "" orelse null isar_deps orelse
  is_blacklisted_or_something ctxt ho_atp (Thm.get_name_hint th)

fun generate_isar_or_prover_commands ctxt prover params_opt thys file_name =
  let
    val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover
    val path = file_name |> Path.explode
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val all_names = build_all_names nickname_of facts
    fun do_fact ((name, ((_, stature), th)), prevs) =
      let
        val feats =
          features_of ctxt prover (theory_of_thm th) stature [prop_of th]
        val isar_deps = isar_dependencies_of all_names th
        val deps =
          isar_or_prover_dependencies_of ctxt params_opt facts all_names th
                                         (SOME isar_deps)
        val core =
          escape_meta name ^ ": " ^ escape_metas prevs ^ "; " ^
          encode_features feats
        val query =
          if is_bad_query ctxt ho_atp th (these isar_deps) then ""
          else "? " ^ core ^ "\n"
        val update = "! " ^ core ^ "; " ^ escape_metas deps ^ "\n"
      in query ^ update end
    val thy_map = old_facts |> thy_map_from_facts
    val parents = fold (add_thy_parent_facts thy_map) thys []
    val new_facts = new_facts |> map (`(nickname_of o snd))
    val prevss = fst (split_last (parents :: map (single o fst) new_facts))
    val lines = Par_List.map do_fact (new_facts ~~ prevss)
  in File.write_list path lines end

fun generate_isar_commands ctxt prover =
  generate_isar_or_prover_commands ctxt prover NONE

fun generate_prover_commands ctxt (params as {provers = prover :: _, ...}) =
  generate_isar_or_prover_commands ctxt prover (SOME params)

fun generate_mepo_suggestions ctxt (params as {provers = prover :: _, ...}) thys
                              max_facts file_name =
  let
    val ho_atp = Sledgehammer_Provers.is_ho_atp ctxt prover
    val path = file_name |> Path.explode
    val facts = all_facts ctxt
    val (new_facts, old_facts) = facts |> List.partition (has_thys thys o snd)
    val all_names = build_all_names nickname_of facts
    fun do_fact ((_, th), old_facts) =
      let
        val name = nickname_of th
        val goal = goal_of_thm (Proof_Context.theory_of ctxt) th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val isar_deps = isar_dependencies_of all_names th
      in
        if is_bad_query ctxt ho_atp th (these isar_deps) then
          ""
        else
          let
            val suggs =
              old_facts
              |> Sledgehammer_MePo.mepo_suggested_facts ctxt params prover
                     max_facts NONE hyp_ts concl_t
              |> map (nickname_of o snd)
          in escape_meta name ^ ": " ^ escape_metas suggs ^ "\n" end
      end
    fun accum x (yss as ys :: _) = (x :: ys) :: yss
    val old_factss = tl (fold accum new_facts [old_facts])
    val lines = Par_List.map do_fact (new_facts ~~ rev old_factss)
  in File.write_list path lines end

end;
