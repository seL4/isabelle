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

(* timing *)

(*a conditional timing function: applies f to () and, if the flag is true,
  prints its runtime*)

fun cond_timeit flag f =
  if flag then
    let
      val before = System.processtime ();
      val result = f ();
      val both = real (System.processtime () - before) / 10.0;
    in
      print ("Process time (incl GC): " ^ makestring both ^ " secs\n");
      result
    end
  else f ();


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp _ pprint (str, blk, brk, en) obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);


(* ML command execution -- 'eval' *)

val use_string =
  let
    fun exec line =
      let
        val is_first = ref true;

        fun get_line () =
          if ! is_first then (is_first := false; line)
          else raise Io "use_string: buffer exhausted";
      in
        PolyML.compiler (get_line, print) ()
      end;

    fun execs [] = ()
      | execs (line :: lines) = (exec line; execs lines);
  in execs end;



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


(* non-ASCII input (see also Thy/symbol_input.ML) *)

val needs_filtered_use =
  (case explode ml_system of
    "p" :: "o" :: "l" :: "y" :: "m" :: "l" :: "-" :: "3" :: _ => true
  | _ => false);
