(* ========================================================================= *)
(* MOSCOW ML SPECIFIC FUNCTIONS                                              *)
(* Copyright (c) 2002-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "mosml";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

local
  val address : 'a -> int = Obj.magic
in
  fun pointerEqual (x : 'a, y : 'a) = address x = address y
end;

(* ------------------------------------------------------------------------- *)
(* Timing function applications.                                             *)
(* ------------------------------------------------------------------------- *)

val time = Mosml.time;

(* ------------------------------------------------------------------------- *)
(* Critical section markup (multiprocessing)                                 *)
(* ------------------------------------------------------------------------- *)

fun CRITICAL e = e ();     (*dummy*)

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  val gen = Random.newgenseed 1.0;
in
  fun randomInt max = Random.range (0,max) gen;

  fun randomReal () = Random.random gen;
end;

fun randomBool () = randomInt 2 = 0;

fun randomWord () =
    let
      val h = Word.fromInt (randomInt 65536)
      and l = Word.fromInt (randomInt 65536)
    in
      Word.orb (Word.<< (h,0w16), l)
    end;

end

(* ------------------------------------------------------------------------- *)
(* Ensuring that interruptions (SIGINTs) are actually seen by the            *)
(* linked executable as Interrupt exceptions.                                *)
(* ------------------------------------------------------------------------- *)

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

(* ------------------------------------------------------------------------- *)
(* Ad-hoc upgrading of the Moscow ML basis library.                          *)
(* ------------------------------------------------------------------------- *)

fun Array_copy {src,dst,di} =
    let
      open Array
    in
      copy {src = src, si = 0, len = NONE, dst = dst, di = di}
    end;

fun Array_foldli f b v =
    let
      open Array
    in
      foldli f b (v,0,NONE)
    end;

fun Array_foldri f b v =
    let
      open Array
    in
      foldri f b (v,0,NONE)
    end;

fun Array_modifyi f a =
    let
      open Array
    in
      modifyi f (a,0,NONE)
    end;

fun TextIO_inputLine h =
    let
      open TextIO
    in
      case inputLine h of "" => NONE | s => SOME s
    end;

fun Vector_foldli f b v =
    let
      open Vector
    in
      foldli f b (v,0,NONE)
    end;

fun Vector_mapi f v =
    let
      open Vector
    in
      mapi f (v,0,NONE)
    end;
