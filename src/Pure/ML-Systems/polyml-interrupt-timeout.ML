(*  Title:      Pure/ML-Systems/polyml-interrupt-timeout.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2006

Bounded time execution (similar to SML/NJ's TimeLimit structure) for Poly/ML.
*)

(* Note: This code may cause an infrequent segmentation fault (due to a race
         condition between process creation/termination and garbage collection)
         before PolyML 5.0. *)

(* Note: f must not manipulate the timer used by Posix.Process.sleep *)

fun interrupt_timeout time f x =
let
  val ch = Process.channel ()
  val interrupt_timer = Process.console (fn () =>
    (Posix.Process.sleep time; Process.send (ch, NONE)))
  val interrupt_worker = Process.console (fn () =>
    Process.send (ch, SOME (capture f x)))
in
  case Process.receive ch of
    NONE    => (interrupt_worker (); raise Interrupt)
  | SOME fx => (interrupt_timer (); release fx)
end;
