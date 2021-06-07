(*  Title:      Pure/ML/ml_profiling.ML
    Author:     Makarius

ML profiling.
*)

signature ML_PROFILING =
sig
  val profile_time: ('a -> 'b) -> 'a -> 'b
  val profile_time_thread: ('a -> 'b) -> 'a -> 'b
  val profile_allocations: ('a -> 'b) -> 'a -> 'b
end;

structure ML_Profiling: ML_PROFILING =
struct

fun profile mode title =
  mode |> PolyML.Profiling.profileStream (fn entries =>
    let
      val body = entries
        |> sort (int_ord o apply2 fst)
        |> map (fn (count, name) =>
            let
              val c = string_of_int count;
              val prefix = replicate_string (Int.max (0, 10 - size c)) " ";
            in prefix ^ c ^ " " ^ name end);
      val total = fold (curry (op +) o fst) entries 0;
    in
      if total = 0 then ()
      else warning (cat_lines (title :: (body @ ["total: " ^ string_of_int total])))
    end);

fun profile_time f =
  profile PolyML.Profiling.ProfileTime "time profile:" f;

fun profile_time_thread f =
  profile PolyML.Profiling.ProfileTimeThisThread "time profile (this thread):" f;

fun profile_allocations f =
  profile PolyML.Profiling.ProfileAllocations "allocations profile:" f;

end;

open ML_Profiling;
