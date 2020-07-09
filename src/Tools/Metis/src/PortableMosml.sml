(* ========================================================================= *)
(* MOSCOW ML SPECIFIC FUNCTIONS                                              *)
(* Copyright (c) 2002 Joe Leslie-Hurd, distributed under the BSD License     *)
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
(* Marking critical sections of code.                                        *)
(* ------------------------------------------------------------------------- *)

fun critical f () = f ();

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

(* ------------------------------------------------------------------------- *)
(* Timing function applications.                                             *)
(* ------------------------------------------------------------------------- *)

val time = Mosml.time;

end

(* ------------------------------------------------------------------------- *)
(* Ensuring that interruptions (SIGINTs) are actually seen by the            *)
(* linked executable as Interrupt exceptions.                                *)
(* ------------------------------------------------------------------------- *)

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

(* ------------------------------------------------------------------------- *)
(* Forcing fully qualified names of functions with generic names.            *)
(* ------------------------------------------------------------------------- *)

(*BasicDebug
val explode = ()
and foldl = ()
and foldr = ()
and implode = ()
and map = ()
and null = ()
and print = ()
and rev = ();
*)

(* ------------------------------------------------------------------------- *)
(* Ad-hoc upgrading of the Moscow ML basis library.                          *)
(* ------------------------------------------------------------------------- *)

fun Real_isFinite (_ : real) = true;
