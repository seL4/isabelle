(* ========================================================================= *)
(* POLY/ML SPECIFIC FUNCTIONS                                                *)
(* Copyright (c) 2008 Joe Hurd, distributed under the BSD License            *)
(* ========================================================================= *)

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "polyml";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

fun pointerEqual (x : 'a, y : 'a) = PolyML.pointerEq(x,y);

(* ------------------------------------------------------------------------- *)
(* Marking critical sections of code.                                        *)
(* ------------------------------------------------------------------------- *)

fun critical f () = f ();

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

val randomWord = Random.nextWord;

val randomBool = Random.nextBool;

val randomInt = Random.nextInt;

val randomReal = Random.nextReal;

(* ------------------------------------------------------------------------- *)
(* Timing function applications.                                             *)
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

end

(* ------------------------------------------------------------------------- *)
(* Quotations a la Moscow ML.                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;
