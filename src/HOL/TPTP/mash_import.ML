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

val freezeT = Type.legacy_freeze_type;

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

val prover_name = ATP_Systems.spassN
val max_relevant = 40
val slack_max_relevant = 2 * max_relevant
val timeout = 2

fun import_and_evaluate_mash_suggestions ctxt thy file_name =
  let
    val params as {relevance_thresholds, ...} =
      Sledgehammer_Isar.default_params ctxt
         [("strict", "true"),
          ("slice", "false"),
          ("timeout", string_of_int timeout),
          ("preplay_timeout", "0"),
          ("minimize", "true")]
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt prover_name
    val relevance_fudge =
      Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover_name
    val relevance_override = {add = [], del = [], only = false}
    val path = file_name |> Path.explode
    val lines = path |> File.read_lines
    val facts = non_tautological_facts_of thy
    val all_names = facts |> map (Thm.get_name_hint o snd)
    val i = 1
    fun run_sh facts goal =
      let
        val facts =
          facts |> take max_relevant
                |> map Sledgehammer_Provers.Untranslated_Fact
        val problem =
          {state = Proof.init ctxt, goal = goal, subgoal = i, subgoal_count = 1,
           facts = facts}
        val prover =
          Sledgehammer_Run.get_minimizing_prover ctxt
              Sledgehammer_Provers.Normal prover_name
      in prover params (K (K (K ""))) problem end
    fun meng_facts goal =
      let val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal i in
        Sledgehammer_Filter.relevant_facts ctxt relevance_thresholds
            slack_max_relevant is_built_in_const relevance_fudge
            relevance_override [] hyp_ts concl_t
      end
    fun find_sugg facts sugg =
      find_first (fn (_, th) => Thm.get_name_hint th = sugg) facts
    fun sugg_facts facts =
      map_filter (find_sugg facts o of_fact_name)
      #> take slack_max_relevant
      #> map (apfst (apfst (fn name => name ())))
    fun hybrid_facts fs1 fs2 =
      let
        val fact_eq = (op =) o pairself fst
        fun score_in f fs =
          case find_index (curry fact_eq f) fs of
            ~1 => length fs
          | j => j
        fun score_of f = score_in f fs1 + score_in f fs2
      in
        union fact_eq fs1 fs2
        |> map (`score_of)
        |> sort (int_ord o pairself fst)
        |> map snd
        |> take max_relevant
      end
    fun with_index facts s =
      (find_index (fn ((s', _), _) => s = s') facts + 1, s)
    fun index_string (j, s) = s ^ "@" ^ string_of_int j
    fun print_res label facts {outcome, run_time, used_facts, ...} =
      tracing ("  " ^ label ^ ": " ^
               (if is_none outcome then
                  "Success (" ^ ATP_Util.string_from_time run_time ^ "): " ^
                  space_implode " "
                      (used_facts |> map (with_index facts o fst)
                                  |> sort (int_ord o pairself fst)
                                  |> map index_string)
                else
                  "Failure: " ^ space_implode " " (map (fst o fst) facts) ))
    fun solve_goal name suggs =
      let
        val name = of_fact_name name
        val _ = tracing ("Goal: " ^ name)
        val th =
          case find_first (fn (_, th) => Thm.get_name_hint th = name) facts of
            SOME (_, th) => th
          | NONE => error ("No fact called \"" ^ name ^ "\"")
        val deps = dependencies_of all_names th
        val goal = th |> prop_of |> freeze |> cterm_of thy |> Goal.init
        val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
        val deps_facts = sugg_facts facts deps
        val meng_facts = meng_facts goal facts
        val mash_facts = sugg_facts facts suggs
        val hybrid_facts = hybrid_facts meng_facts mash_facts
        val deps_res = run_sh deps_facts goal
        val meng_res = run_sh meng_facts goal
        val mash_res = run_sh mash_facts goal
        val hybrid_res = run_sh hybrid_facts goal
      in
        print_res "Dependencies" deps_facts deps_res;
        print_res "Meng & Paulson" meng_facts meng_res;
        print_res "MaSh" mash_facts mash_res;
        print_res "Hybrid" hybrid_facts hybrid_res
      end
    val explode_suggs = space_explode " " #> filter_out (curry (op =) "")
    fun do_line line =
      case space_explode ":" line of
        [goal_name, suggs] => solve_goal goal_name (explode_suggs suggs)
      | _ => ()
  in List.app do_line lines end

end;
