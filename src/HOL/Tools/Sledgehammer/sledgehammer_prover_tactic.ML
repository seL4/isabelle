(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Martin Desharnais, LMU Muenchen

Isabelle tactics as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_TACTIC =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type prover = Sledgehammer_Prover.prover
  type base_slice = Sledgehammer_ATP_Systems.base_slice

  val fact_classification_dest_dir : string Config.T
  val fact_classification_prefix : string Config.T

  val is_tactic_prover : Proof.context -> string -> bool
  val good_slices_of_tactic_prover : string -> base_slice list
  val run_tactic_prover : mode -> string -> prover
end;

structure Sledgehammer_Prover_Tactic : SLEDGEHAMMER_PROVER_TACTIC =
struct

open ATP_Problem_Generate
open ATP_Proof
open Sledgehammer_Proof_Methods
open Sledgehammer_Prover

val fact_classification_dest_dir =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_fact_classification_dest_dir\<close> (K "")
val fact_classification_prefix =
  Attrib.setup_config_string \<^binding>\<open>sledgehammer_fact_classification_prefix\<close>
    (K "fact_classification")

fun is_tactic_prover (ctxt : Proof.context) (name : string) : bool =
  is_some (Try0.get_proof_method ctxt name)

local

val slices_of_max_facts = map (fn max_facts => (1, false, false, max_facts, "mesh"))

in

(* FUDGE *)
fun good_slices_of_tactic_prover "metis" = slices_of_max_facts [0, 64, 32, 8, 16, 4, 2, 1]
  | good_slices_of_tactic_prover "fastforce" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover "simp" = slices_of_max_facts [0, 16, 32, 8, 64, 4, 1, 2]
  | good_slices_of_tactic_prover "auto" = slices_of_max_facts [0, 16, 32, 8, 4, 64, 2, 1]
  | good_slices_of_tactic_prover _ = slices_of_max_facts [0, 2, 8, 16, 32, 64]

end

fun meth_of "algebra" = Algebra_Method
  | meth_of "argo" = Argo_Method
  | meth_of "auto" = Auto_Method
  | meth_of "blast" = Blast_Method
  | meth_of "fastforce" = Fastforce_Method
  | meth_of "force" = Force_Method
  | meth_of "linarith" = Linarith_Method
  | meth_of "meson" = Meson_Method
  | meth_of "metis" = Metis_Method (NONE, NONE, [])
  | meth_of "order" = Order_Method
  | meth_of "presburger" = Presburger_Method
  | meth_of "satx" = SATx_Method
  | meth_of "simp" = Simp_Method
  | meth_of _ = Metis_Method (NONE, NONE, [])

fun collapse_whitespace (s : string) : string = implode_space (String.tokens Char.isSpace s)

fun string_of_tactic_outcome (outcome : atp_failure option) : string =
  (case outcome of
    NONE => "success"
  | SOME TimedOut => "timed_out"
  | SOME _ => "gave_up")

val class_width = fold (Integer.max o size) Try0.native_classes 0
val kind_width = size "direct"

fun make_fact_lines (facts : Try0.facts) : string list =
  let
    fun make_fact_line class kind xref =
      implode_space ["fact", StringCvt.padRight #" " class_width class,
        StringCvt.padRight #" " kind_width kind,
        collapse_whitespace (Try0_Util.string_of_xref xref)]
    fun make_xxrefs_lines class {usings, directs} =
      map (make_fact_line class "using") usings @ map (make_fact_line class "direct") directs
  in
    maps (uncurry make_xxrefs_lines) (Symtab.dest (#classified facts)) @
    make_xxrefs_lines "-" (#unclassified facts)
  end

fun write_fact_classification_log (ctxt : Proof.context) (prover : string) (mode : mode)
    (max_facts : int) (classifier_time : Time.time) (method_time : Time.time)
    (outcome : atp_failure option) (command : string) (facts : Try0.facts) : unit =
  let
    val command = collapse_whitespace (Protocol_Message.clean_output command)
    val slice_fields =
      [Context.theory_long_name (Proof_Context.theory_of ctxt), prover, str_of_mode mode,
       string_of_int max_facts, string_of_int (Time.toMicroseconds classifier_time),
       string_of_int (Time.toMicroseconds method_time), string_of_tactic_outcome outcome] @
      (if command = "" then [] else [command])
    val file_name =
      Config.get ctxt fact_classification_prefix ^ "__" ^ prover ^ "_" ^ string_of_int max_facts ^
      "__" ^ serial_string ()
    val dir =
      Isabelle_System.make_directory (Path.explode (Config.get ctxt fact_classification_dest_dir))
    val lines = implode_space ("slice" :: slice_fields) :: make_fact_lines facts
  in
    File.write (dir + Path.basic file_name) (cat_lines lines ^ "\n")
  end

fun run_tactic_prover mode name ({slices, timeout, ...} : params)
    ({state, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) slice =
  let
    val (basic_slice as (slice_size, _, _, max_facts, _), No_Slice) = slice
    val facts = facts_of_basic_slice basic_slice factss
    val non_chained = filter_out is_fact_chained facts
    val ctxt = Proof.context_of state

    fun classify_facts () =
      let
        val (locals, globals) = List.partition (fn ((_, (sc, _)), _) => sc <> Global) non_chained
        fun is_cartouche str = String.isPrefix "\<open>" str andalso String.isSuffix "\<close>" str
        fun xref_of_fact (((name, _), thm) : Sledgehammer_Fact.fact) =
          let
            val xref =
              if is_cartouche name then
                Facts.Fact (Pretty.pure_string_of (Thm.pretty_thm ctxt thm))
              else
                (case try (unsuffix ")") name of
                  SOME s' =>
                  (case ATP_Util.first_field_substring "(" (Substring.full s') of
                    SOME (name', num) =>
                    (case Int.fromString (Substring.string num) of
                      SOME n =>
                      Facts.Named ((Substring.string name', Position.none), SOME [Facts.Single n])
                    | NONE => Facts.named name)
                  | NONE => Facts.named name)
                | NONE => Facts.named name)
          in
            (xref, [])
          end
        val usings_xrefs = map xref_of_fact (sort_by (fst o fst) locals)
        val direct_xrefs = map xref_of_fact (sort_by (fst o fst) globals)
      in
        {unclassified = {usings = usings_xrefs, directs = direct_xrefs}, classified = Symtab.empty}
        |> Try0.classify_facts ctxt
      end

    fun run_proof_method facts =
      (case Try0.get_proof_method_or_noop ctxt name
          (SOME (slice_timeout slice_size slices timeout)) facts state of
        NONE => (SOME GaveUp, "")
      | SOME {command, ...} => (NONE, command))
      handle ERROR _ => (SOME GaveUp, "")
           | Timeout.TIMEOUT _ => (SOME TimedOut, "")

    fun classify_facts_and_run_proof_method () =
      (case (SOME (Timing.timing classify_facts ()) handle ERROR _ => NONE) of
        NONE => (SOME GaveUp, "")
      | SOME ({elapsed = classifier_time, ...}, classified_facts) =>
          let
            val ({elapsed = method_time, ...}, (outcome, command)) =
              Timing.timing run_proof_method classified_facts
            val () =
              if Config.get ctxt fact_classification_dest_dir = "" then ()
              else
                write_fact_classification_log ctxt name mode max_facts classifier_time method_time
                  outcome command classified_facts
          in
            (outcome, command)
          end)

    val timer = Timer.startRealTimer ()
    val (outcome, command) = classify_facts_and_run_proof_method ()
    val run_time = Timer.checkRealTimer timer

    val used_facts =
      (case outcome of
        NONE => (found_something name; map fst non_chained)
      | SOME _ => [])

    val message = fn preplay_outcome =>
      (case outcome of
        NONE =>
        let
          val banner = proof_banner mode name
        in
          (case preplay_outcome of
            NONE => try_command_line banner (Played run_time) command
          | SOME preplay_result =>
              one_line_proof_text (preplay_result, banner, subgoal, subgoal_count))
        end
      | SOME failure => string_of_atp_failure failure)
  in
    {outcome = outcome, used_facts = used_facts, used_from = facts,
     preferred_methss = (meth_of name, []), run_time = run_time, message = message}
  end

end;
