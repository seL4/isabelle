(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (versions 2.x and 3.x).
*)

open PolyML ExtendedIO;

(*needs the Basis Library emulation*)
use "basis.ML";



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

fun use_text txt =
  let
    val buffer = ref (explode txt);
    fun get () =
      (case ! buffer of
        [] => ""
      | c :: cs => (buffer := cs; c));
    fun exec () =
      (case ! buffer of
        [] => ()
      | _ => (PolyML.compiler (get, print) (); exec ()));
  in exec () end;



(** OS related **)

local

fun drop_last [] = []
  | drop_last [x] = []
  | drop_last (x :: xs) = x :: drop_last xs;

val drop_last_char = implode o drop_last o explode;

in


(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout*)
fun execute command =
  let
    val (is, os) =  ExtendedIO.execute command;
    val result = input (is, 999999);
  in
    close_out os;
    close_in is;
    result
  end;


(* file handling *)

(*get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""		(* FIXME !? *)
  | file_info name = Int.toString (System.filedate name) handle _ => "";

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


(* non-ASCII input (see also Thy/use.ML) *)

val needs_filtered_use =
  (case explode ml_system of
    "p" :: "o" :: "l" :: "y" :: "m" :: "l" :: "-" :: "3" :: _ => true
  | _ => false);
