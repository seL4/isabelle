(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML (after 5.1).
*)

use "ML-Systems/polyml_common.ML";
use "ML-Systems/multithreading_polyml.ML";

val pointer_eq = PolyML.pointerEq;


(* single-threaded profiling *)

local val profile_orig = profile in

fun profile 0 f x = f x
  | profile n f x = NAMED_CRITICAL "profile" (fn () => profile_orig n f x);

end;


(* improved versions of use_text/file *)

fun use_text (tune: string -> string) (line, name) (print, err) verbose txt =
  let
    val in_buffer = ref (String.explode (tune txt));
    val out_buffer = ref ([]: string list);
    fun output () = implode (rev (case ! out_buffer of "\n" :: cs => cs | cs => cs));

    val current_line = ref line;
    fun get () =
      (case ! in_buffer of
        [] => NONE
      | c :: cs =>
          (in_buffer := cs; if c = #"\n" then current_line := ! current_line + 1 else (); SOME c));
    fun put s = out_buffer := s :: ! out_buffer;

    val _ =
      (while not (List.null (! in_buffer)) do
        PolyML.compiler
          {getChar = get, putString = put, lineNumber = fn () => ! current_line, fileName = name,
            nameSpace = PolyML.globalNameSpace} ())
      handle exn => (err (output ()); raise exn);
  in
    if verbose then print (output ()) else ()
  end;

fun use_file tune output verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = TextIO.inputAll instream before TextIO.closeIn instream;
  in use_text tune (1, name) output verbose txt end;

