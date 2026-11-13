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

fun split_list_map_filter _ [] = ([], [])
  | split_list_map_filter f (x :: xs) =
      (case f x of
        NONE => split_list_map_filter f xs
      | SOME (y, z) =>
          let val (ys, zs) = split_list_map_filter f xs
          in (y :: ys, z :: zs) end)

val class_width = fold (Integer.max o size) Try0.native_classes 0
val kind_width = size "direct"

fun make_fact_lines (facts : Try0.xref Try0.facts) : string list =
  let
    fun make_fact_line class kind xref =
      implode_space ["fact", StringCvt.padRight #" " class_width class,
        StringCvt.padRight #" " kind_width kind,
        collapse_whitespace (Try0_Util.string_of_xref xref)]
    fun make_usings_directs_lines class {usings, directs} =
      map (make_fact_line class "using") usings @ map (make_fact_line class "direct") directs
  in
    maps (uncurry make_usings_directs_lines) (Symtab.dest (#classified facts)) @
    make_usings_directs_lines "-" (#unclassified facts)
  end

fun write_fact_classification_log (ctxt : Proof.context) (prover : string) (mode : mode)
    (max_facts : int) (classifier_time : Time.time) (method_time : Time.time)
    (outcome : atp_failure option) (command : string) (facts : Try0.xref Try0.facts) : unit =
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

local

fun is_cartouche (str : string) : bool =
  String.isPrefix "\<open>" str andalso String.isSuffix "\<close>" str

fun literal_xref_of_fact (ctxt : Proof.context) (thm : thm) : Facts.ref option =
  let
    val xref = Facts.Fact (Pretty.pure_string_of (Thm.pretty_thm ctxt thm))
  in
    (* A fact referred to by its statement must be retrievable from that text in "ctxt". This
       fails, e.g., if the statement mentions a fixed variable that is shadowed by another one with
       the same name; such a fact cannot be referred to in a proof text at all. *)
    (case try (Proof_Context.get_fact ctxt) xref of
      SOME [thm'] => if Thm.eq_thm_prop (thm, thm') then SOME xref else NONE
    | _ => NONE)
  end

(* Parses fact names of the form "foo(3)" as a selection of the third theorem of "foo". *)
fun named_xref_of_name (name : string) : Facts.ref =
  let val default = Facts.named name in
    if String.isSuffix ")" name then
      (case ATP_Util.first_field_substring "(" (Substring.trimr 1 (Substring.full name)) of
        SOME (name', num) =>
          (case Int.scan StringCvt.DEC Substring.getc num of
            SOME (n, rest) =>
              if Substring.isEmpty rest then
                Facts.Named ((Substring.string name', Position.none), SOME [Facts.Single n])
              else
                default
          | NONE => default)
      | NONE => default)
    else
      default
  end

val _ = \<^assert> (named_xref_of_name "foo" = Facts.named "foo")
val _ = \<^assert>
  (named_xref_of_name "foo(3)" = Facts.Named (("foo", Position.none), SOME [Facts.Single 3]))
val _ = \<^assert> (named_xref_of_name "foo(3abc)" = Facts.named "foo(3abc)")
val _ = \<^assert> (named_xref_of_name "foo(bar)" = Facts.named "foo(bar)")
val _ = \<^assert> (named_xref_of_name "foo)" = Facts.named "foo)")

in

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
        fun with_xref (fact as ((name, _), thm) : Sledgehammer_Fact.fact) =
          if is_cartouche name then
            (case literal_xref_of_fact ctxt thm of
              SOME xref => SOME (fact, (xref, []))
            | NONE => NONE)
          else
            SOME (fact, (named_xref_of_name name, []))
        val (referable_local_facts, usings) =
          split_list_map_filter with_xref (sort_by (fst o fst) locals)
        val (referable_global_facts, directs) =
          split_list_map_filter with_xref (sort_by (fst o fst) globals)
      in
        (Try0.unclassified_facts {usings = usings, directs = directs}
         |> Try0.classify_facts state, referable_local_facts, referable_global_facts)
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
        NONE => ((SOME GaveUp, ""), [], [], NONE)
      | SOME ({elapsed = classifier_time, ...},
          (classified_facts, referable_local_facts, referable_global_facts)) =>
          let
            val ({elapsed = method_time, ...}, (outcome, command)) =
              Timing.timing run_proof_method classified_facts
          in
            ((outcome, command), referable_local_facts, referable_global_facts,
             SOME (classifier_time, method_time, classified_facts))
          end)

    val ({elapsed = run_time, ...},
         ((outcome, command), referable_local_facts, referable_global_facts, classification)) =
      Timing.timing classify_facts_and_run_proof_method ()

    (* The log is written outside of the timed region so that it does not inflate "run_time". *)
    val () =
      (case classification of
        SOME (classifier_time, method_time, classified_facts) =>
          if Config.get ctxt fact_classification_dest_dir = "" then
            ()
          else
            write_fact_classification_log ctxt name mode max_facts classifier_time method_time
              outcome command classified_facts
      | NONE => ())

    val used_facts =
      (case outcome of
        NONE =>
          (found_something name;
           fold_rev (cons o fst) referable_local_facts (map fst referable_global_facts))
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

end

end;
