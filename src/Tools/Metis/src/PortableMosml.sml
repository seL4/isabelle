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

local val address : 'a -> int = Obj.magic
in fun pointerEqual (x : 'a, y : 'a) = address x = address y
end;

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
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
(* Ad-hoc upgrading of the Moscow ML basis library.                          *)
(* ------------------------------------------------------------------------- *)

fun TextIO_inputLine h =
    let
      open TextIO
    in
      case inputLine h of "" => NONE | s => SOME s
    end;
