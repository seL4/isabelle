(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (versions 2.x and 3.x).
*)

open PolyML ExtendedIO;

(*needs the Basis Library emulation*)
use "basis.ML";


structure String =
struct
  fun substring (s,i,j) = StringBuiltIns.substring (s, i+1, j)
                          handle Substring => raise Subscript
  fun isPrefix s1 s2 = (s1 = substring(s2,0, size s1))
                       handle Subscript => false
end;


(** ML system related **)

(** Compiler-independent timing functions **)

(*Note start point for timing*)
fun startTiming() = System.processtime ();

(*Finish timing and return string*)
fun endTiming before =
  "User + GC: " ^
  makestring (real (System.processtime () - before) / 10.0) ^
  " secs";


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp _ pprint (str, blk, brk, en) obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);


(* ML command execution -- 'eval' *)

local

fun drop_last [] = []
  | drop_last [x] = []
  | drop_last (x :: xs) = x :: drop_last xs;

val drop_last_char = implode o drop_last o explode;

in

fun use_text (print, err) verbose txt =
  let
    val in_buffer = ref (explode txt);
    val out_buffer = ref ([]: string list);
    fun output () = drop_last_char (implode (rev (! out_buffer)));

    fun get () =
      (case ! in_buffer of
        [] => ""
      | c :: cs => (in_buffer := cs; c));
    fun put s = out_buffer := s :: ! out_buffer;

    fun exec () =
      (case ! in_buffer of
        [] => ()
      | _ => (PolyML.compiler (get, put) (); exec ()));
  in
    exec () handle exn => (err (output ()); raise exn);
    if verbose then print (output ()) else ()
  end;



(** interrupts **)      (*Note: may get into race conditions*)

fun ignore_interrupt f x = f x;
fun raise_interrupt f x = f x;



(** OS related **)

(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout*)
fun execute command =
  let
    val (is, os) =  ExtendedIO.execute command;
    val _ = close_out os;
    val result = input (is, 999999);
  in close_in is; result end;

fun system cmd = (print (execute cmd); 0);	(* FIXME rc not available *)


(* file handling *)

(*get time of last modification*)
fun file_info name = Int.toString (System.filedate name) handle _ => "";

structure OS =
struct
  structure FileSys =
  struct
    val chDir = PolyML.cd;
    fun remove name = (execute ("rm " ^ name); ());
    fun getDir () = drop_last_char (execute "pwd");
  end;
end;


(* getenv *)

fun getenv var = drop_last_char
  (execute ("env | grep '^" ^ var ^ "=' | sed -e 's/" ^ var ^ "=//'"));


end;
