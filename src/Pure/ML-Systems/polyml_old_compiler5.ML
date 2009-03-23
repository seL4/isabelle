(*  Title:      Pure/ML-Systems/polyml_old_compiler5.ML

Runtime compilation -- for old PolyML.compilerEx (version 5.0, 5.1).
*)

fun use_text ({tune_source, print, error, ...}: use_context) (line, name) verbose txt =
  let
    val in_buffer = ref (explode (tune_source txt));
    val out_buffer = ref ([]: string list);
    fun output () = implode (rev (case ! out_buffer of "\n" :: cs => cs | cs => cs));

    val current_line = ref line;
    fun get () =
      (case ! in_buffer of
        [] => ""
      | c :: cs => (in_buffer := cs; if c = "\n" then current_line := ! current_line + 1 else (); c));
    fun put s = out_buffer := s :: ! out_buffer;

    fun exec () =
      (case ! in_buffer of
        [] => ()
      | _ => (PolyML.compilerEx (get, put, fn () => ! current_line, name) (); exec ()));
  in
    exec () handle exn => (error (output ()); raise exn);
    if verbose then print (output ()) else ()
  end;

fun use_file context verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text context (1, name) verbose txt end;
