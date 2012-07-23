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

fun use_theories name options =
  Thy_Info.use_thys
    |> Session.with_timing name (Options.bool options "timing")
    |> Unsynchronized.setmp Proofterm.proofs (Options.int options "proofs")
    |> Unsynchronized.setmp print_mode
        (space_explode "," (Options.string options "print_mode") @ print_mode_value ())
    |> Unsynchronized.setmp Goal.parallel_proofs (Options.int options "parallel_proofs")
    |> Unsynchronized.setmp Goal.parallel_proofs_threshold
        (Options.int options "parallel_proofs_threshold")
    |> Unsynchronized.setmp Multithreading.trace (Options.int options "threads_trace")
    |> Unsynchronized.setmp Multithreading.max_threads (Options.int options "threads_limit");

fun build args_file =
  let
    val (save, (options, (verbose, (browser_info, (parent, (name, (base_name, theories))))))) =
      File.read (Path.explode args_file) |> YXML.parse_body |>
        let open XML.Decode in
          pair bool (pair Options.decode (pair bool (pair string (pair string
            (pair string (pair string ((list (pair Options.decode (list string))))))))))
        end;

    val _ =
      Session.init
        save
        false (* FIXME reset!? *)
        (Options.bool options "browser_info") browser_info
        (Options.string options "document_format")   (* FIXME dependent on "document" (!?) *)
        (Options.bool options "document_graph")
        (space_explode "," (Options.string options "document_variants"))
        parent
        base_name
        (true (* FIXME copy document/ files on Scala side!? *),
          Options.string options "document_dump")
        ""
        verbose;

    val _ = List.app (uncurry (use_theories name)) theories;
    val _ = Session.finish ();

    val _ = if save then () else quit ();
  in () end
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;
