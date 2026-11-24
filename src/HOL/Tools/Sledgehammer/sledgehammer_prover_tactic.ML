(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML
    Author:     Jasmin Blanchette, LMU Muenchen
    Author:     Martin Desharnais, LMU Muenchen

Isabelle tactics as Sledgehammer provers.
*)

signature SLEDGEHAMMER_PROVER_TACTIC =
sig
  type stature = ATP_Problem_Generate.stature
  type mode = Sledgehammer_Prover.mode
  type params = Sledgehammer_Prover.params
  type prover_problem = Sledgehammer_Prover.prover_problem
  type prover_slice = Sledgehammer_Prover.prover_slice
  type prover_result = Sledgehammer_Prover.prover_result
  type base_slice = Sledgehammer_ATP_Systems.base_slice

  val fact_classification_dest_dir : string Config.T
  val fact_classification_prefix : string Config.T

  val is_tactic_prover : Proof.context -> string -> bool
  val good_slices_of_tactic_prover : string -> base_slice list
  val run_tactic_prover : mode -> params -> prover_problem -> string -> prover_slice ->
    prover_result
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

(* FUDGE *)
val tactic_prover_max_facts = 64

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

local

fun collapse_whitespace (s : string) : string = implode_space (String.tokens Char.isSpace s)

fun string_of_tactic_outcome (outcome : atp_failure option) : string =
  (case outcome of
    NONE => "success"
  | SOME TimedOut => "timed_out"
  | SOME _ => "gave_up")

val class_width = fold (Integer.max o size) Try0.native_classes 0

fun dest_facts ({unclassified, classified} : Try0.xref Try0.facts) :
    (string * string * string) list =
  let
    fun add_fact class kind xref =
      cons (class, kind, collapse_whitespace (Try0_Util.string_of_xref xref))
    fun add_usings_directs class {usings, directs} =
      fold_rev (add_fact class "using") usings o fold_rev (add_fact class "direct") directs
  in
    []
    |> add_usings_directs "-" unclassified
    |> Symtab.fold_rev (uncurry add_usings_directs) classified
  end

fun add_column (width : int) (str : string) : Bytes.T -> Bytes.T =
  if size str > width then
    Bytes.add " " o Bytes.add str
  else
    Bytes.add (StringCvt.padRight #" " (width + 1) str)

fun add_fact_lines (input_facts : Try0.xref Try0.facts) (output_facts : Try0.xref Try0.facts)
    (bytes : Bytes.T) : Bytes.T =
  let
    val inputs = dest_facts input_facts
    val outputs = dest_facts output_facts
    fun make_names facts = Symtab.build (fold (fn (_, _, name) => Symtab.insert_set name) facts)
    val input_names = make_names inputs
    val output_names = make_names outputs
    fun add_fact_line marks (class, kind, name) bytes =
      bytes
      |> Bytes.add marks
      |> add_column class_width class
      |> add_column 6 kind
      |> Bytes.add name
      |> Bytes.add "\n"
    fun add_output_line (fact as (_, _, name)) =
      add_fact_line (if Symtab.defined input_names name then "in out " else "-  out ") fact
    fun add_removed_input_line (fact as (_, _, name)) =
      if Symtab.defined output_names name then I else add_fact_line "in -   " fact
  in
    bytes
    |> fold add_output_line outputs
    |> fold add_removed_input_line inputs
  end

in

fun write_fact_classification_log (ctxt : Proof.context) (prover : string) (mode : mode)
    (max_facts : int) (classifier_time : Time.time) (method_time : Time.time)
    (outcome : atp_failure option) (command : string) (input_facts : Try0.xref Try0.facts)
    (output_facts : Try0.xref Try0.facts) : unit =
  let
    val command = collapse_whitespace (Protocol_Message.clean_output command)
    fun add_field field bytes = bytes |> Bytes.add " " |> Bytes.add field
    fun add_slice_line bytes =
      bytes
      |> Bytes.add "slice"
      |> add_field (Context.theory_long_name (Proof_Context.theory_of ctxt))
      |> add_field prover
      |> add_field (str_of_mode mode)
      |> add_field (string_of_int max_facts)
      |> add_field (string_of_int (Time.toMicroseconds classifier_time))
      |> add_field (string_of_int (Time.toMicroseconds method_time))
      |> add_field (string_of_tactic_outcome outcome)
      |> (if command = "" then I else add_field command)
      |> Bytes.add "\n"
    val file_name =
      Config.get ctxt fact_classification_prefix ^ "__" ^ prover ^ "_" ^ string_of_int max_facts ^
      "__" ^ serial_string ()
    val dir =
      Isabelle_System.make_directory (Path.explode (Config.get ctxt fact_classification_dest_dir))
  in
    Bytes.empty
    |> add_slice_line
    |> add_fact_lines input_facts output_facts
    |> Bytes.write (dir + Path.basic file_name)
  end

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

fun run_tactic_prover mode ({max_facts, slices, timeout, ...} : params)
    ({state, subgoal, subgoal_count, factss, found_something, ...} : prover_problem) =
  let
    val ctxt = Proof.context_of state
    val log_classification = Config.get ctxt fact_classification_dest_dir <> ""

    val verified_literal_xrefs =
      let val num_facts = the_default tactic_prover_max_facts max_facts in
        fold (fn (fact_filter, _) =>
            facts_of_basic_slice (1, false, false, num_facts, fact_filter) factss
            |> fold (fn fact as ((name, _), thm) => fn xrefs =>
              if is_cartouche name andalso not (is_fact_chained fact)
                 andalso not (Symtab.defined xrefs name) then
                Symtab.update_new (name, literal_xref_of_fact ctxt thm) xrefs
              else
                xrefs))
          factss Symtab.empty
      end

    fun with_xref (fact as ((name, _), thm) : Sledgehammer_Fact.fact) =
      (if is_cartouche name then
         (case Symtab.lookup verified_literal_xrefs name of
           SOME xref => xref
         | NONE => literal_xref_of_fact ctxt thm)
       else
         SOME (named_xref_of_name name))
      |> Option.map (fn xref => (fact, (xref, [])))

    fun classify_facts non_chained =
      let
        val (locals, globals) = List.partition (fn ((_, (sc, _)), _) => sc <> Global) non_chained
        val (referable_local_facts, usings) =
          split_list (map_filter with_xref (sort_by (fst o fst) locals))
        val (referable_global_facts, directs) =
          split_list (map_filter with_xref (sort_by (fst o fst) globals))
        val input_facts = Try0.unclassified_facts {usings = usings, directs = directs}
      in
        (input_facts, Try0.classify_facts state input_facts, referable_local_facts,
         referable_global_facts)
      end

    val slice_facts = Synchronized.var "slice_facts" []

    (* the facts of a slice and their classification, which depend only on the fact filter and
       the number of facts *)
    fun slice_facts_of fact_filter num_facts =
      Synchronized.change_result slice_facts (fn entries =>
        (case AList.lookup (op =) entries (fact_filter, num_facts) of
          SOME entry => (entry, entries)
        | NONE =>
            let
              val entry = Lazy.lazy (fn () =>
                let
                  val facts = facts_of_basic_slice (1, false, false, num_facts, fact_filter) factss
                  val classification =
                    SOME (Timing.timing classify_facts (filter_out is_fact_chained facts))
                    handle ERROR _ => NONE
                in (facts, classification) end)
            in (entry, ((fact_filter, num_facts), entry) :: entries) end))
      |> Lazy.force
  in
    fn name =>
      let
        val proof_method = Try0.get_proof_method_or_noop ctxt name
      in
        fn ((slice_size, _, _, slice_max_facts, fact_filter), _) =>
          let
            fun run_proof_method facts =
              (case proof_method (SOME (slice_timeout slice_size slices timeout)) facts state of
                NONE => (SOME GaveUp, "")
              | SOME {command, ...} => (NONE, command))
              handle ERROR _ => (SOME GaveUp, "")
                   | Timeout.TIMEOUT _ => (SOME TimedOut, "")

            fun classify_facts_and_run_proof_method () =
              let val (facts, classification) = slice_facts_of fact_filter slice_max_facts in
                (case classification of
                  NONE => (facts, (SOME GaveUp, ""), [], [], NONE)
                | SOME ({elapsed = classifier_time, ...},
                    (input_facts, classified_facts, referable_local_facts,
                     referable_global_facts)) =>
                    let
                      val ({elapsed = method_time, ...}, (outcome, command)) =
                        Timing.timing run_proof_method classified_facts
                    in
                      (facts, (outcome, command), referable_local_facts, referable_global_facts,
                       SOME (classifier_time, method_time, input_facts, classified_facts))
                    end)
              end

            val ({elapsed = run_time, ...},
                 (facts, (outcome, command), referable_local_facts, referable_global_facts,
                  classification)) =
              Timing.timing classify_facts_and_run_proof_method ()

            (* The log is written outside of the timed region so that it does not inflate
               "run_time". *)
            val () =
              (case classification of
                SOME (classifier_time, method_time, input_facts, classified_facts) =>
                  if log_classification then
                    write_fact_classification_log ctxt name mode slice_max_facts classifier_time
                      method_time outcome command input_facts classified_facts
                  else
                    ()
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
                  let val banner = proof_banner mode name in
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
  end

end

end;
