(*  Title:      Pure/PIDE/command_span.ML
    Author:     Makarius

Syntactic representation of command spans.
*)

signature COMMAND_SPAN =
sig
  datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span
  datatype span = Span of kind * Token.T list
  val kind: span -> kind
  val content: span -> Token.T list
  val position: span -> Position.T
  val symbol_length: span -> int
end;

structure Command_Span: COMMAND_SPAN =
struct

datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span;
datatype span = Span of kind * Token.T list;

fun kind (Span (k, _)) = k;
fun content (Span (_, toks)) = toks;

fun position (Span (Command_Span (_, pos), _)) = pos
  | position _ = Position.none;

fun symbol_length span =
  (case Position.distance_of (Token.range_of (content span)) of
    SOME n => n
  | NONE => raise Fail ("Undefined length of command span" ^ Position.here (position span)));

end;
