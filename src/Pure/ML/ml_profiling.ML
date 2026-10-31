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
  val tracing: {kind: string} -> {name: string, count: int} list -> unit
  val kind_time: string
  val kind_time_thread: string
  val kind_allocations: string
  val check_mode: string -> unit
  val profile: string -> ('a -> 'b) -> 'a -> 'b
  include BASIC_ML_PROFILING
end;

structure ML_Profiling: ML_PROFILING =
struct

(* XML markup *)

fun markup_entry entry =
  if #count entry = 0 then NONE
  else SOME (XML.Elem (Markup.ML_profiling_entry entry, []));

fun markup_body kind body =
  if null body then []
  else [XML.Elem (Markup.ML_profiling kind, body)];

fun tracing {kind} entries =
  (case map_filter markup_entry entries of
    [] => ()
  | body => Output.tracings (Bytes.contents (YXML.bytes_of_body (markup_body kind body))));


(* kinds *)

val kind_time = "time";
val kind_time_thread = "time_thread";
val kind_allocations = "allocations";


(* Poly/ML mode *)

val modes =
  Symtab.make
    [(kind_time, PolyML.Profiling.ProfileTime),
     (kind_time_thread, PolyML.Profiling.ProfileTimeThisThread),
     (kind_allocations, PolyML.Profiling.ProfileAllocations)];

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
        val output =
          sort (int_ord o apply2 fst)
          #> map (fn (count, name) => {name = name, count = count})
          #> tracing {kind = kind};
      in PolyML.Profiling.profileStream output mode f x end;

fun profile_time f = profile kind_time f;
fun profile_time_thread f = profile kind_time_thread f;
fun profile_allocations f = profile kind_allocations f;

end;

structure Basic_ML_Profiling: BASIC_ML_PROFILING = ML_Profiling;
open Basic_ML_Profiling;
