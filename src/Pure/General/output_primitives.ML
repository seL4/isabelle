(*  Title:      Pure/General/output_primitives.ML
    Author:     Makarius

Primitives for Isabelle output channels.
*)

signature OUTPUT_PRIMITIVES =
sig
  structure XML:
  sig
    type attributes = (string * string) list
    datatype tree =
        Elem of (string * attributes) * tree list
      | Text of string
    type body = tree list
  end
  type output = string
  type serial = int
  type properties = (string * string) list
  val ignore_outputs: output list -> unit
  val writeln_fn: output list -> unit
  val state_fn: output list -> unit
  val information_fn: output list -> unit
  val tracing_fn: output list -> unit
  val warning_fn: output list -> unit
  val legacy_fn: output list -> unit
  val error_message_fn: serial * output list -> unit
  val system_message_fn: output list -> unit
  val status_fn: output list -> unit
  val report_fn: output list -> unit
  val result_fn: properties -> output list -> unit
  type protocol_message_fn = properties -> XML.body list -> unit
  val protocol_message_fn: protocol_message_fn
  val markup_fn: string * properties -> output * output
end;

structure Output_Primitives: OUTPUT_PRIMITIVES =
struct

(** XML trees **)

structure XML =
struct

type attributes = (string * string) list;

datatype tree =
    Elem of (string * attributes) * tree list
  | Text of string;

type body = tree list;

end;


(* output *)

type output = string;
type serial = int;
type properties = (string * string) list;

fun ignore_outputs (_: output list) = ();

val writeln_fn = ignore_outputs;
val state_fn = ignore_outputs;
val information_fn = ignore_outputs;
val tracing_fn = ignore_outputs;
val warning_fn = ignore_outputs;
val legacy_fn = ignore_outputs;
fun error_message_fn (_: serial, _: output list) = ();
val system_message_fn = ignore_outputs;
val status_fn = ignore_outputs;
val report_fn = ignore_outputs;
fun result_fn (_: properties) = ignore_outputs;

type protocol_message_fn = properties -> XML.body list -> unit;
val protocol_message_fn: protocol_message_fn = fn _ => fn _ => ();

fun markup_fn (_: string * properties) = ("", "");

end;
