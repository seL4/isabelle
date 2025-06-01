(*  Title:      Pure/PIDE/command_span.ML
    Author:     Makarius

Syntactic representation of command spans.
*)

signature COMMAND_SPAN =
sig
  val extensions: string list -> Path.T -> Path.T list
  datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span
  datatype span = Span of kind * Token.T list
  val kind: span -> kind
  val content: span -> Token.T list
  val symbol_length: span -> int option
  val eof: span
  val is_eof: span -> bool
  val stopper: span Scan.stopper
  val adjust_offsets_kind: (int -> int option) -> kind -> kind
  val adjust_offsets: (int -> int option) -> span -> span
end;

structure Command_Span: COMMAND_SPAN =
struct

(* loaded files *)

fun extensions exts path = map (fn ext => Path.ext ext path) exts;


(* span *)

datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span;
datatype span = Span of kind * Token.T list;

fun kind (Span (k, _)) = k;
fun content (Span (_, toks)) = toks;
val symbol_length = Position.distance_of o Token.range_of o content;


(* stopper *)

val eof = Span (Command_Span ("", Position.none), []);

fun is_eof (Span (Command_Span ("", _), _)) = true
  | is_eof _ = false;

val stopper = Scan.stopper (K eof) is_eof;


(* presentation positions *)

fun adjust_offsets_kind adjust k =
  (case k of
    Command_Span (name, pos) => Command_Span (name, Position.adjust_offsets adjust pos)
  | _ => k);

fun adjust_offsets adjust (Span (k, toks)) =
  Span (adjust_offsets_kind adjust k, map (Token.adjust_offsets adjust) toks);

end;
