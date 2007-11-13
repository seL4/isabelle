(* ========================================================================= *)
(* POLYML SPECIFIC FUNCTIONS                                                 *)
(* Copyright (c) 2002-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

CM.autoload "$smlnj/init/init.cmi";

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "SmlNJ";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

fun pointerEqual (x : 'a, y : 'a) = InlineT.ptreql (x,y);

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
(* ------------------------------------------------------------------------- *)

fun time f x =
  let
    fun p t =
      let
        val s = Time.fmt 3 t
      in
        case size (List.last (String.fields (fn x => x = #".") s)) of 3 => s
        | 2 => s ^ "0"
        | 1 => s ^ "00"
        | _ => raise Fail "Portable.time"
      end
    val c = Timer.startCPUTimer ()
    val r = Timer.startRealTimer ()
    fun pt () =
      let
        val {sys, usr} = Timer.checkCPUTimer c
        val real = Timer.checkRealTimer r
      in
        print
        ("User: " ^ p usr ^ "  System: " ^ p sys ^
         "  Real: " ^ p real ^ "\n")
      end
    val y = f x handle e => (pt (); raise e)
    val () = pt ()
  in
    y
  end;

(* ------------------------------------------------------------------------- *)
(* Critical section markup (multiprocessing)                                 *)
(* ------------------------------------------------------------------------- *)

fun CRITICAL e = e ();     (*dummy*)

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

fun randomWord () = MLton.Random.rand ();

fun randomBool () = Word.andb (randomWord (),0w1) = 0w0;

fun randomInt 1 = 0
  | randomInt 2 = Word.toInt (Word.andb (randomWord (), 0w1))
  | randomInt 4 = Word.toInt (Word.andb (randomWord (), 0w3))
  | randomInt n = Word.toInt (Word.mod (randomWord (), Word.fromInt n));

local
  fun wordToReal w = Real.fromInt (Word.toInt (Word.>> (w,0w1)))

  val normalizer = 1.0 / wordToReal (Word.notb 0w0);
in
  fun randomReal () = normalizer * wordToReal (randomWord ());
end;

end

(* ------------------------------------------------------------------------- *)
(* Quotations a la Moscow ML.                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;
