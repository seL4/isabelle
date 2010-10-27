(*  Title:      Pure/General/output.ML
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Output channels and timing messages.
*)

signature BASIC_OUTPUT =
sig
  val writeln: string -> unit
  val tracing: string -> unit
  val warning: string -> unit
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
  type output = string
  val default_output: string -> output * int
  val default_escape: output -> string
  val add_mode: string -> (string -> output * int) -> (output -> string) -> unit
  val output_width: string -> output * int
  val output: string -> output
  val escape: output -> string
  val raw_stdout: output -> unit
  val raw_stderr: output -> unit
  val raw_writeln: output -> unit
  structure Private_Hooks:
  sig
    val writeln_fn: (output -> unit) Unsynchronized.ref
    val urgent_message_fn: (output -> unit) Unsynchronized.ref
    val tracing_fn: (output -> unit) Unsynchronized.ref
    val warning_fn: (output -> unit) Unsynchronized.ref
    val error_fn: (output -> unit) Unsynchronized.ref
    val prompt_fn: (output -> unit) Unsynchronized.ref
    val status_fn: (output -> unit) Unsynchronized.ref
    val report_fn: (output -> unit) Unsynchronized.ref
  end
  val urgent_message: string -> unit
  val error_msg: string -> unit
  val prompt: string -> unit
  val status: string -> unit
  val report: string -> unit
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

(* raw output primitives -- not to be used in user-space *)

fun raw_stdout s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
fun raw_stderr s = (TextIO.output (TextIO.stdErr, s); TextIO.flushOut TextIO.stdErr);

fun raw_writeln "" = ()
  | raw_writeln s = raw_stdout (suffix "\n" s);  (*atomic output!*)


(* Isabelle output channels *)

structure Private_Hooks =
struct
  val writeln_fn = Unsynchronized.ref raw_writeln;
  val urgent_message_fn = Unsynchronized.ref (fn s => ! writeln_fn s);
  val tracing_fn = Unsynchronized.ref (fn s => ! writeln_fn s);
  val warning_fn = Unsynchronized.ref (raw_stdout o suffix "\n" o prefix_lines "### ");
  val error_fn = Unsynchronized.ref (raw_stdout o suffix "\n" o prefix_lines "*** ");
  val prompt_fn = Unsynchronized.ref raw_stdout;
  val status_fn = Unsynchronized.ref (fn _: string => ());
  val report_fn = Unsynchronized.ref (fn _: string => ());
end;

fun writeln s = ! Private_Hooks.writeln_fn (output s);
fun urgent_message s = ! Private_Hooks.urgent_message_fn (output s);
fun tracing s = ! Private_Hooks.tracing_fn (output s);
fun warning s = ! Private_Hooks.warning_fn (output s);
fun error_msg s = ! Private_Hooks.error_fn (output s);
fun prompt s = ! Private_Hooks.prompt_fn (output s);
fun status s = ! Private_Hooks.status_fn (output s);
fun report s = ! Private_Hooks.report_fn (output s);

fun legacy_feature s = warning ("Legacy feature! " ^ s);



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
