(*  Title:      Pure/General/output.ML
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Output channels and timing messages.
*)

signature BASIC_OUTPUT =
sig
  type output = string
  val writeln: string -> unit
  val priority: string -> unit
  val tracing: string -> unit
  val warning: string -> unit
  val tolerate_legacy_features: bool Unsynchronized.ref
  val legacy_feature: string -> unit
  val cond_timeit: bool -> string -> (unit -> 'a) -> 'a
  val timeit: (unit -> 'a) -> 'a
  val timeap: ('a -> 'b) -> 'a -> 'b
  val timeap_msg: string -> ('a -> 'b) -> 'a -> 'b
  val timing: bool Unsynchronized.ref
end;

signature OUTPUT =
sig
  include BASIC_OUTPUT
  val default_output: string -> output * int
  val default_escape: output -> string
  val add_mode: string -> (string -> output * int) -> (output -> string) -> unit
  val output_width: string -> output * int
  val output: string -> output
  val escape: output -> string
  val std_output: output -> unit
  val std_error: output -> unit
  val writeln_default: output -> unit
  val writeln_fn: (output -> unit) Unsynchronized.ref
  val priority_fn: (output -> unit) Unsynchronized.ref
  val tracing_fn: (output -> unit) Unsynchronized.ref
  val warning_fn: (output -> unit) Unsynchronized.ref
  val error_fn: (output -> unit) Unsynchronized.ref
  val debug_fn: (output -> unit) Unsynchronized.ref
  val prompt_fn: (output -> unit) Unsynchronized.ref
  val status_fn: (output -> unit) Unsynchronized.ref
  val error_msg: string -> unit
  val prompt: string -> unit
  val status: string -> unit
  val debugging: bool Unsynchronized.ref
  val no_warnings_CRITICAL: ('a -> 'b) -> 'a -> 'b
  val debug: (unit -> string) -> unit
end;

structure Output: OUTPUT =
struct

(** print modes **)

type output = string;  (*raw system output*)

fun default_output s = (s, size s);
fun default_escape (s: output) = s;

local
  val default = {output = default_output, escape = default_escape};
  val modes = Unsynchronized.ref (Symtab.make [("", default)]);
in
  fun add_mode name output escape = CRITICAL (fn () =>
    Unsynchronized.change modes (Symtab.update_new (name, {output = output, escape = escape})));
  fun get_mode () =
    the_default default (Library.get_first (Symtab.lookup (! modes)) (print_mode_value ()));
end;

fun output_width x = #output (get_mode ()) x;
val output = #1 o output_width;

fun escape x = #escape (get_mode ()) x;



(** output channels **)

(* output primitives -- normally NOT used directly!*)

fun std_output s = NAMED_CRITICAL "IO" (fn () =>
  (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut));

fun std_error s = NAMED_CRITICAL "IO" (fn () =>
  (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr));

fun writeln_default "" = ()
  | writeln_default s = std_output (suffix "\n" s);


(* Isabelle output channels *)

val writeln_fn = Unsynchronized.ref writeln_default;
val priority_fn = Unsynchronized.ref (fn s => ! writeln_fn s);
val tracing_fn = Unsynchronized.ref (fn s => ! writeln_fn s);
val warning_fn = Unsynchronized.ref (std_output o suffix "\n" o prefix_lines "### ");
val error_fn = Unsynchronized.ref (std_output o suffix "\n" o prefix_lines "*** ");
val debug_fn = Unsynchronized.ref (std_output o suffix "\n" o prefix_lines "::: ");
val prompt_fn = Unsynchronized.ref std_output;
val status_fn = Unsynchronized.ref (fn _: string => ());

fun writeln s = ! writeln_fn (output s);
fun priority s = ! priority_fn (output s);
fun tracing s = ! tracing_fn (output s);
fun warning s = ! warning_fn (output s);
fun error_msg s = ! error_fn (output s);
fun prompt s = ! prompt_fn (output s);
fun status s = ! status_fn (output s);

val tolerate_legacy_features = Unsynchronized.ref true;
fun legacy_feature s =
  (if ! tolerate_legacy_features then warning else error) ("Legacy feature! " ^ s);

fun no_warnings_CRITICAL f = setmp_CRITICAL warning_fn (K ()) f;

val debugging = Unsynchronized.ref false;
fun debug s = if ! debugging then ! debug_fn (output (s ())) else ()



(** timing **)

(*conditional timing with message*)
fun cond_timeit flag msg e =
  if flag then
    let
      val start = start_timing ();
      val result = Exn.capture e ();
      val end_msg = #message (end_timing start);
      val _ = warning (if msg = "" then end_msg else msg ^ "\n" ^ end_msg);
    in Exn.release result end
  else e ();

(*unconditional timing*)
fun timeit e = cond_timeit true "" e;

(*timed application function*)
fun timeap f x = timeit (fn () => f x);
fun timeap_msg msg f x = cond_timeit true msg (fn () => f x);

(*global timing mode*)
val timing = Unsynchronized.ref false;

end;

structure Basic_Output: BASIC_OUTPUT = Output;
open Basic_Output;
