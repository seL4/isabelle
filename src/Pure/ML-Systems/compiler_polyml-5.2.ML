(*  Title:      Pure/ML-Systems/compiler_polyml-5.2.ML

Runtime compilation for Poly/ML 5.2 and 5.2.1.
*)

local

fun drop_newline s =
  if String.isSuffix "\n" s then String.substring (s, 0, size s - 1)
  else s;

in

fun use_text ({tune_source, name_space, str_of_pos, print, error, ...}: use_context)
    (start_line, name) verbose txt =
  let
    val current_line = ref start_line;
    val in_buffer = ref (String.explode (tune_source txt));
    val out_buffer = ref ([]: string list);
    fun output () = drop_newline (implode (rev (! out_buffer)));

    fun get () =
      (case ! in_buffer of
        [] => NONE
      | c :: cs =>
          (in_buffer := cs; if c = #"\n" then current_line := ! current_line + 1 else (); SOME c));
    fun put s = out_buffer := s :: ! out_buffer;
    fun message (msg, is_err, line) =
      (if is_err then "Error: " else "Warning: ") ^ drop_newline msg ^ str_of_pos line name ^ "\n";

    val parameters =
     [PolyML.Compiler.CPOutStream put,
      PolyML.Compiler.CPLineNo (fn () => ! current_line),
      PolyML.Compiler.CPErrorMessageProc (put o message),
      PolyML.Compiler.CPNameSpace name_space];
    val _ =
      (while not (List.null (! in_buffer)) do
        PolyML.compiler (get, parameters) ())
      handle exn =>
       (put ("Exception- " ^ General.exnMessage exn ^ " raised");
        error (output ()); raise exn);
  in if verbose then print (output ()) else () end;

fun use_file context verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = Exn.release (Exn.capture TextIO.inputAll instream before TextIO.closeIn instream);
  in use_text context (1, name) verbose txt end;

end;

