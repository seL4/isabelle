(*  Title:      Pure/ML-Systems/polyml-5.0.ML
    ID:         $Id$

Compatibility wrapper for Poly/ML 5.1.
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



(** multithreading **)

open Thread;

local

datatype 'a result =
  Result of 'a |
  Exn of exn;

fun capture f x = Result (f x) handle e => Exn e;

fun release (Result y) = y
  | release (Exn e) = raise e;

fun message s =
  (TextIO.output (TextIO.stdErr, (">>> " ^ s ^ "\n")); TextIO.flushOut TextIO.stdErr);


val critical_lock = Mutex.mutex ();
val critical_thread = ref (NONE: Thread.thread option);

in

(* critical section -- may be nested within the same thread *)

fun self_critical () =
  (case ! critical_thread of
    NONE => false
  | SOME id => Thread.equal (id, Thread.self ()));

fun CRITICAL e =
  if self_critical () then e ()
  else
    let
      val _ =
        if Mutex.trylock critical_lock then ()
        else
          (message "Waiting for critical lock";
           Mutex.lock critical_lock;
           message "Obtained critical lock");
      val _ = critical_thread := SOME (Thread.self ());
      val res = capture e ();
      val _ = critical_thread := NONE;
      val _ = Mutex.unlock critical_lock;
    in release res end;

end;
