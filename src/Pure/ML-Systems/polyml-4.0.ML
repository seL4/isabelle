(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (versions 2.x and 3.x).
*)

(** ML system related **)

open PolyML;


(* restore old-style character / string functions *)

fun ord s = Char.ord (String.sub (s, 0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(*Note start point for timing*)
fun startTiming() =
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

(*Finish timing and return string*)
fun endTiming (CPUtimer, {sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  All "^ toString (sys2-sys + usr2-usr) ^
      " secs"
      handle Time => ""
  end;


(* prompts *)

fun ml_prompts p1 p2 = (PolyML.Compiler.prompt1 := p1; PolyML.Compiler.prompt2 := p2);


(* toplevel pretty printing (see also Pure/install_pp.ML) *)

fun make_pp path pprint = ();
fun install_pp _ = ();
(* FIXME
fun make_pp _ pprint (str, blk, brk, en) obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);
*)


(* ML command execution -- 'eval' *)

local

fun drop_last [] = []
  | drop_last [x] = []
  | drop_last (x :: xs) = x :: drop_last xs;

val drop_last_char = implode o drop_last o explode;

in

fun use_text print verbose txt =
  let
    val in_buffer = ref (explode txt);
    val out_buffer = ref ([]: string list);

    fun get () =
      (case ! in_buffer of
        [] => ""
      | c :: cs => (in_buffer := cs; c));
    fun put s = out_buffer := s :: ! out_buffer;

    fun exec () =
      (case ! in_buffer of
        [] => ()
      | _ => (PolyML.compiler (get, put) (); exec ()));

    fun show_output () = print (drop_last_char (implode (rev (! out_buffer))));
  in
    exec () handle exn => (show_output (); raise exn);
    if verbose then show_output () else ()
  end;

end;



(** interrupts **)      (*Note: may get into race conditions*)

fun mask_interrupt f x = f x;
fun unmask_interrupt f x = f x;
fun exhibit_interrupt f x = f x;



(** OS related **)

(* system command execution *)

(*execute Unix command which doesn't take any input from stdin and
  sends its output to stdout; could be done more easily by Unix.execute,
  but that function doesn't use the PATH*)
fun execute command =
  let
    val tmp_name = OS.FileSys.tmpName ();
    val is = (OS.Process.system (command ^ " > " ^ tmp_name); TextIO.openIn tmp_name);
    val result = TextIO.inputAll is;
  in
    TextIO.closeIn is;
    OS.FileSys.remove tmp_name;
    result
  end;

(*plain version; with return code*)
fun system cmd =
  if OS.Process.isSuccess (OS.Process.system cmd) then 0 else 1;


(* file handling *)

(*get time of last modification*)
fun file_info name = Time.toString (OS.FileSys.modTime name) handle _ => "";


(* getenv *)

fun getenv var =
  (case OS.Process.getEnv var of
    NONE => ""
  | SOME txt => txt);


(* non-ASCII input (see also Thy/use.ML) *)

val needs_filtered_use = true;
