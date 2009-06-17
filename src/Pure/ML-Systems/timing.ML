(*  Title:      Pure/ML-Systems/timing.ML
    Author:     Makarius

Compiler-independent timing functions.
*)

fun start_timing () =
  let
    val real_timer = Timer.startRealTimer ();
    val real_time = Timer.checkRealTimer real_timer;
    val cpu_timer = Timer.startCPUTimer ();
    val cpu_times = Timer.checkCPUTimes cpu_timer;
  in (real_timer, real_time, cpu_timer, cpu_times) end;

fun end_timing (real_timer, real_time, cpu_timer, cpu_times) =
  let
    val real_time2 = Timer.checkRealTimer real_timer;
    val {nongc = {sys, usr}, gc = {sys = gc_sys, usr = gc_usr}} = cpu_times;
    val {nongc = {sys = sys2, usr = usr2}, gc = {sys = gc_sys2, usr = gc_usr2}} =
      Timer.checkCPUTimes cpu_timer;

    open Time;
    val elapsed = real_time2 - real_time;
    val gc = gc_usr2 - gc_usr + gc_sys2 - gc_sys;
    val cpu = usr2 - usr + sys2 - sys + gc;
    val gc_ratio = Real.fmt (StringCvt.FIX (SOME 2)) (toReal gc / toReal cpu);
    val factor = Real.fmt (StringCvt.FIX (SOME 2)) (toReal cpu / toReal elapsed);
    val message =
      (toString elapsed ^ "s elapsed time, " ^ toString cpu ^ "s cpu time, " ^
        gc_ratio ^ "% GC time, factor " ^ factor) handle Time => "";
  in {message = message, elapsed = elapsed, cpu = cpu, gc = gc} end;

