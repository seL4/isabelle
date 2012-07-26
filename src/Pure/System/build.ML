(*  Title:      Pure/System/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

signature BUILD =
sig
  val build: string -> unit
end;

structure Build: BUILD =
struct

local

fun no_document options =
  (case Options.string options "document" of "" => true | "false" => true | _ => false) andalso
  (Options.string options "document_dump" = "");

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
    |> no_document options ? Present.no_document
    |> Unsynchronized.setmp quick_and_dirty (Options.bool options "quick_and_dirty")
    |> Unsynchronized.setmp Printer.show_question_marks_default
        (Options.bool options "show_question_marks")
    |> Unsynchronized.setmp Name_Space.names_long_default (Options.bool options "names_long")
    |> Unsynchronized.setmp Name_Space.names_short_default (Options.bool options "names_short")
    |> Unsynchronized.setmp Name_Space.names_unique_default (Options.bool options "names_unique")
    |> Unsynchronized.setmp Toplevel.timing (Options.bool options "timing");

fun use_theories (options, thys) =
  let val condition = space_explode "," (Options.string options "condition") in
    (case filter_out (can getenv_strict) condition of
      [] => use_thys options thys
    | conds =>
        Output.physical_stderr ("Ignoring theories " ^ commas_quote thys ^
          " (undefined " ^ commas conds ^ ")\n"))
  end;

in

fun build args_file =
  let
    val (do_output, (options, (timing, (verbose, (browser_info, (parent_base_name,
        (name, (base_name, theories)))))))) =
      File.read (Path.explode args_file) |> YXML.parse_body |>
        let open XML.Decode in
          pair bool (pair Options.decode (pair bool (pair bool (pair string (pair string
            (pair string (pair string ((list (pair Options.decode (list string)))))))))))
        end;

    val _ =
      Session.init do_output false
        (Options.bool options "browser_info") browser_info
        (Options.string options "document")
        (Options.bool options "document_graph")
        (space_explode ":" (Options.string options "document_variants"))
        parent_base_name base_name
        (not (Options.bool options "document_dump_only"), Options.string options "document_dump")
        (Options.string options "browser_info_remote")
        verbose;
    val _ = Session.with_timing name timing (List.app use_theories) theories;
    val _ = Session.finish ();
    val _ = if do_output then () else quit ();
  in () end
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;

end;
