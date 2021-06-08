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

fun print_entry count name =
  let
    val c = string_of_int count;
    val prefix = Symbol.spaces (Int.max (0, 10 - size c));
  in prefix ^ c ^ " " ^ name end;

fun profile mode kind title f x =
  PolyML.Profiling.profileStream (fn entries =>
    (case fold (curry (op +) o fst) entries 0 of
      0 => ()
    | total =>
        let
          val body = entries
            |> sort (int_ord o apply2 fst)
            |> map (fn (count, name) =>
                let val markup = Markup.ML_profiling_entry {name = name, count = count}
                in XML.Elem (markup, [XML.Text (print_entry count name ^ "\n")]) end);
          val xml =
            XML.Elem (Markup.ML_profiling kind,
              XML.Text (title ^ "\n") :: body @ [XML.Text (print_entry total "TOTAL")]);
        in tracing (YXML.string_of xml) end)) mode f x;

fun profile_time f =
  profile PolyML.Profiling.ProfileTime "time" "time profile:" f;

fun profile_time_thread f =
  profile PolyML.Profiling.ProfileTimeThisThread "time_thread" "time profile (single thread):" f;

fun profile_allocations f =
  profile PolyML.Profiling.ProfileAllocations "allocations" "allocations profile:" f;

end;

open ML_Profiling;
