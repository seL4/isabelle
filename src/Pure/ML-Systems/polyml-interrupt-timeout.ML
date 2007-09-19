(*  Title:      Pure/ML-Systems/polyml-interrupt-timeout.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2006-2007

Bounded time execution (similar to SML/NJ's TimeLimit structure) for Poly/ML.
*)

(* Note: This code may cause an infrequent segmentation fault (due to a race
         condition between process creation/termination and garbage collection)
         before PolyML 5.0. *)

(* Note: The timer process sometimes does not receive enough CPU time to put
         itself to sleep.  It then cannot indicate a timeout when (or soon
         after) the specified time has elapsed.  This issue is obviously caused
         by the process scheduling algorithm in current PolyML versions.  We
         could use additional communication between the timer and the worker
         process to ensure that the timer receives /some/ CPU time, but there
         seems to be no way to guarantee that the timer process receives
         sufficient CPU time to complete its task. *)

(* Note: f must not manipulate the timer used by Posix.Process.sleep *)

fun interrupt_timeout time f x =
let
  val ch = Process.channel ()
  val interrupt_timer = Process.console (fn () =>
    (Posix.Process.sleep time; Process.send (ch, NONE)))
  val interrupt_worker = Process.console (fn () =>
    Process.send (ch, SOME (Exn.capture f x)))
in
  case Process.receive ch of
    NONE    => (interrupt_worker (); raise Interrupt)
  | SOME fx => (interrupt_timer (); Exn.release fx)
end;
