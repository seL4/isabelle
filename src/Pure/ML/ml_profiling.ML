(*  Title:      Pure/ML/ml_profiling.ML
    Author:     Makarius

ML profiling (via Poly/ML run-time system).
*)

signature BASIC_ML_PROFILING =
sig
  val profile_time: ('a -> 'b) -> 'a -> 'b
  val profile_time_thread: ('a -> 'b) -> 'a -> 'b
  val profile_allocations: ('a -> 'b) -> 'a -> 'b
end;

signature ML_PROFILING =
sig
  val check_mode: string -> unit
  val profile: string -> ('a -> 'b) -> 'a -> 'b
  include BASIC_ML_PROFILING
end;

structure ML_Profiling: ML_PROFILING =
struct

(* mode *)

val modes =
  Symtab.make
    [("time", PolyML.Profiling.ProfileTime),
     ("time_thread", PolyML.Profiling.ProfileTimeThisThread),
     ("allocations", PolyML.Profiling.ProfileAllocations)];

fun get_mode kind =
  (case Symtab.lookup modes kind of
    SOME mode => mode
  | NONE => error ("Bad profiling mode: " ^ quote kind));

fun check_mode "" = ()
  | check_mode kind = ignore (get_mode kind);


(* profile *)

fun profile "" f x = f x
  | profile kind f x =
      let
        val mode = get_mode kind;
        fun output entries =
          let
            val body = entries
              |> sort (int_ord o apply2 fst)
              |> map_filter (fn (n, name) =>
                  if n = 0 then NONE
                  else SOME (XML.Elem (Markup.ML_profiling_entry {name = name, count = n}, [])));
          in
            if null body then ()
            else tracing (YXML.string_of (XML.Elem (Markup.ML_profiling kind, body)))
          end;
      in PolyML.Profiling.profileStream output mode f x end;

fun profile_time f = profile "time" f;
fun profile_time_thread f = profile "time_thread" f;
fun profile_allocations f = profile "allocations" f;

end;

structure Basic_ML_Profiling: BASIC_ML_PROFILING = ML_Profiling;
open Basic_ML_Profiling;
