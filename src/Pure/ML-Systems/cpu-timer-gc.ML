(*  Title:      Pure/ML-Systems/cpu-timer-gc.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)

Implementation of timing functions, building on implementations where
the return type of Timer.checkCPUTimer includes a gc field.
*)

(*Note start point for timing*)
fun startTiming() =
  let val CPUtimer = Timer.startCPUTimer();
      val time = Timer.checkCPUTimer(CPUtimer)
  in  (CPUtimer,time)  end;

(*Finish timing and return string*)
fun endTiming (CPUtimer, {gc,sys,usr}) =
  let open Time  (*...for Time.toString, Time.+ and Time.- *)
      val {gc=gc2,sys=sys2,usr=usr2} = Timer.checkCPUTimer(CPUtimer)
  in  "User " ^ toString (usr2-usr) ^
      "  GC " ^ toString (gc2-gc) ^
      "  All "^ toString (sys2-sys + usr2-usr + gc2-gc) ^
      " secs"
      handle Time => ""
  end;

