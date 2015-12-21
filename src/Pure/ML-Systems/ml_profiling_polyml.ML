(*  Title:      Pure/ML-Systems/ml_profiling_polyml.ML
    Author:     Makarius

Profiling for Poly/ML.
*)

structure ML_Profiling =
struct

local

fun profile n f x =
  let
    val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
    val res = Exn.capture f x;
    val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;
  in Exn.release res end;

in

fun profile_time (_: (int * string) list -> unit) f x = profile 1 f x;
fun profile_time_thread (_: (int * string) list -> unit) f x = profile 6 f x;
fun profile_allocations (_: (int * string) list -> unit) f x = profile 2 f x;

end;

end;
