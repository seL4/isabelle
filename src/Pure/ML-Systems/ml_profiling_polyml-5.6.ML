(*  Title:      Pure/ML-Systems/ml_profiling_polyml-5.6.ML
    Author:     Makarius

Profiling for Poly/ML 5.6.
*)

fun profile 0 f x = f x
  | profile n f x =
      let
        val mode =
          (case n of
            1 => PolyML.Profiling.ProfileTime
          | 2 => PolyML.Profiling.ProfileAllocations
          | 3 => PolyML.Profiling.ProfileLongIntEmulation
          | 6 => PolyML.Profiling.ProfileTimeThisThread
          | _ => raise Fail ("Bad profile mode: " ^ Int.toString n));
      in PolyML.Profiling.profile mode f x end;
