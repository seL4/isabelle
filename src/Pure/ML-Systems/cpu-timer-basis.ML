(*  Title:      Pure/ML-Systems/cpu-timer-basis.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

Implementation of timing functions, building on standard ("basis library") functions.
*)

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

