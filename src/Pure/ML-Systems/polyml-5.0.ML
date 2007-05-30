(*  Title:      Pure/ML-Systems/polyml-5.0.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.0.
*)

use "ML-Systems/polyml.ML";

val pointer_eq = PolyML.pointerEq;


(* improved versions of use_text/file *)

fun use_text name (print, err) verbose txt =
  let
    val in_buffer = ref (explode txt);
    val out_buffer = ref ([]: string list);
    fun output () = implode (rev (case ! out_buffer of "\n" :: cs => cs | cs => cs));

    val line_no = ref 1;
    fun line () = ! line_no;
    fun get () =
      (case ! in_buffer of
        [] => ""
      | c :: cs => (in_buffer := cs; if c = "\n" then line_no := ! line_no + 1 else (); c));
    fun put s = out_buffer := s :: ! out_buffer;

    fun exec () =
      (case ! in_buffer of
        [] => ()
      | _ => (PolyML.compilerEx (get, put, line, name) (); exec ()));
  in
    exec () handle exn => (err (output ()); raise exn);
    if verbose then print (output ()) else ()
  end;

fun use_file output verbose name =
  let
    val instream = TextIO.openIn name;
    val txt = TextIO.inputAll instream before TextIO.closeIn instream;
  in use_text name output verbose txt end;
