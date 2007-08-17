(* ========================================================================= *)
(* MLTON SPECIFIC FUNCTIONS                                                  *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "mlton";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

val pointerEqual = MLton.eq;

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
(* ------------------------------------------------------------------------- *)

fun time f x =
    let
      fun p t =
          let
            val s = Time.fmt 3 t
          in
            case size (List.last (String.fields (fn x => x = #".") s)) of
              3 => s
            | 2 => s ^ "0"
            | 1 => s ^ "00"
            | _ => raise Fail "Portable.time"
          end

      val c = Timer.startCPUTimer ()

      val r = Timer.startRealTimer ()

      fun pt () =
          let
            val {usr,sys} = Timer.checkCPUTimer c
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

end

(* ------------------------------------------------------------------------- *)
(* Quotations a la Moscow ML.                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;
