(*  Title:      Pure/ML-Systems/polyml-interrupt-timeout.ML
    ID:         $Id$
    Author:     Tjark Weber, Makarius
    Copyright   2006

Bounded time execution (similar to SML/NJ's TimeLimit structure) for Poly/ML.
*)

(* FIXME: this code appears to disable signal handling in child databases altogether (?)
local

  val alarm_active = ref false;

  val _ = Signal.signal (Posix.Signal.alrm, Signal.SIG_HANDLE (fn _ =>
    let val active = ! alarm_active in
      alarm_active := false;
      if active then
        Process.interruptConsoleProcesses ()
      else
        ()
    end));

in

  fun interrupt_timeout time f x =
  let
    fun deactivate_alarm () = (
      alarm_active := false;
      Posix.Process.alarm Time.zeroTime
    )
  in
    alarm_active := true;
    Posix.Process.alarm time;
    let val result = f x in
      deactivate_alarm ();
      result
    end handle exn => (
      deactivate_alarm ();
      raise exn
    )
  end;

end;
*)

fun interrupt_timeout time f x =
  f x;
