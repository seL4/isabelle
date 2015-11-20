(*  Title:      Pure/ML-Systems/ml_profiling_polyml.ML
    Author:     Makarius

Profiling for Poly/ML.
*)

fun profile 0 f x = f x
  | profile n f x =
      let
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler n;
        val res = Exn.capture f x;
        val _ = RunCall.run_call1 RuntimeCalls.POLY_SYS_profiler 0;
      in Exn.release res end;
