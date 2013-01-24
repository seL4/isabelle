(*  Title:      Pure/Tools/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

signature BUILD =
sig
  val build: string -> unit
end;

structure Build: BUILD =
struct

(* protocol messages *)

local

fun ML_statistics (function :: stats) "" =
      if function = Markup.ML_statistics then SOME stats
      else NONE
  | ML_statistics _ _ = NONE;

fun task_statistics (function :: stats) "" =
      if function = Markup.task_statistics then SOME stats
      else NONE
  | task_statistics _ _ = NONE;

val print_properties = YXML.string_of_body o XML.Encode.properties;

in

fun protocol_message props output =
  (case ML_statistics props output of
    SOME stats => writeln ("\fML_statistics = " ^ print_properties stats)
  | NONE =>
      (case task_statistics props output of
        SOME stats => writeln ("\ftask_statistics = " ^ print_properties stats)
      | NONE =>
          (case Markup.dest_loading_theory props of
            SOME name => writeln ("\floading_theory = " ^ name)
          | NONE => raise Fail "Undefined Output.protocol_message")));

end;


(* build *)

local

fun no_document options =
  (case Options.string options "document" of "" => true | "false" => true | _ => false);

fun use_thys options =
  Thy_Info.use_thys
    |> Unsynchronized.setmp Proofterm.proofs (Options.int options "proofs")
    |> Unsynchronized.setmp print_mode
        (space_explode "," (Options.string options "print_mode") @ print_mode_value ())
    |> Unsynchronized.setmp Goal.parallel_proofs (Options.int options "parallel_proofs")
    |> Unsynchronized.setmp Goal.parallel_proofs_threshold
        (Options.int options "parallel_proofs_threshold")
    |> Unsynchronized.setmp Multithreading.trace (Options.int options "threads_trace")
    |> Unsynchronized.setmp Multithreading.max_threads (Options.int options "threads")
    |> Unsynchronized.setmp Future.ML_statistics true
    |> no_document options ? Present.no_document
    |> Unsynchronized.setmp quick_and_dirty (Options.bool options "quick_and_dirty")
    |> Unsynchronized.setmp Toplevel.skip_proofs (Options.bool options "skip_proofs")
    |> Unsynchronized.setmp Printer.show_question_marks_default
        (Options.bool options "show_question_marks")
    |> Unsynchronized.setmp Name_Space.names_long_default (Options.bool options "names_long")
    |> Unsynchronized.setmp Name_Space.names_short_default (Options.bool options "names_short")
    |> Unsynchronized.setmp Name_Space.names_unique_default (Options.bool options "names_unique")
    |> Unsynchronized.setmp Thy_Output.display_default (Options.bool options "thy_output_display")
    |> Unsynchronized.setmp Thy_Output.quotes_default (Options.bool options "thy_output_quotes")
    |> Unsynchronized.setmp Thy_Output.indent_default (Options.int options "thy_output_indent")
    |> Unsynchronized.setmp Thy_Output.source_default (Options.bool options "thy_output_source")
    |> Unsynchronized.setmp Thy_Output.break_default (Options.bool options "thy_output_break")
    |> Unsynchronized.setmp Pretty.margin_default (Options.int options "pretty_margin")
    |> Unsynchronized.setmp Toplevel.timing (Options.bool options "timing");

fun use_theories (options, thys) =
  let val condition = space_explode "," (Options.string options "condition") in
    (case filter_out (can getenv_strict) condition of
      [] => use_thys options (map (rpair Position.none) thys)
    | conds =>
        Output.physical_stderr ("Skipping theories " ^ commas_quote thys ^
          " (undefined " ^ commas conds ^ ")\n"))
  end;

in

fun build args_file = Command_Line.tool (fn () =>
    let
      val (do_output, (options, (verbose, (browser_info, (parent_name,
          (name, theories)))))) =
        File.read (Path.explode args_file) |> YXML.parse_body |>
          let open XML.Decode in
            pair bool (pair Options.decode (pair bool (pair string (pair string
              (pair string ((list (pair Options.decode (list string)))))))))
          end;

      val document_variants =
        map Present.read_variant (space_explode ":" (Options.string options "document_variants"));
      val _ =
        (case duplicates (op =) (map fst document_variants) of
          [] => ()
        | dups => error ("Duplicate document variants: " ^ commas_quote dups));

      val _ = writeln ("\fSession.name = " ^ name);
      val _ =
        (case Session.path () of
          [] => ()
        | path => writeln ("\fSession.parent_path = " ^ space_implode "/" path));
      val _ =
        Session.init do_output false
          (Options.bool options "browser_info") browser_info
          (Options.string options "document")
          (Options.bool options "document_graph")
          (Options.string options "document_output")
          document_variants
          parent_name name
          (false, "") ""
          verbose;

      val res1 =
        theories |>
          (List.app use_theories
            |> Session.with_timing name verbose
            |> Unsynchronized.setmp Output.Private_Hooks.protocol_message_fn protocol_message
            |> Unsynchronized.setmp Multithreading.max_threads (Options.int options "threads")
            |> Exn.capture);
      val res2 = Exn.capture Session.finish ();
      val _ = Par_Exn.release_all [res1, res2];

      val _ = if do_output then () else exit 0;
    in 0 end);

end;

end;
