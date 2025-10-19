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
  val is_ignored: span -> bool
  val content: span -> Token.T list
  val range: span -> Position.range
  val symbol_length: span -> int option
  val eof: span
  val is_eof: span -> bool
  val stopper: span Scan.stopper
  val adjust_offsets_kind: (int -> int option) -> kind -> kind
  val adjust_offsets: (int -> int option) -> span -> span
  val command_ranges: span list -> Position.range list
end;

structure Command_Span: COMMAND_SPAN =
struct

(* loaded files *)

fun extensions exts path = map (fn ext => Path.ext ext path) exts;


(* span *)

datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span;
datatype span = Span of kind * Token.T list;

fun kind (Span (k, _)) = k;
fun is_ignored span = kind span = Ignored_Span;
fun content (Span (_, toks)) = toks;
val range = Token.range_of o content;
val symbol_length = Position.distance_of o range;


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


(* command ranges, including trailing non-commands (whitespace etc.) *)

fun command_ranges spans =
  let
    fun ranges NONE [] result = rev result
      | ranges (SOME pos) [] result =
          let val end_pos = #2 (range (List.last spans))
          in rev (Position.range (pos, end_pos) :: result) end
      | ranges start_pos (span :: rest) result =
          (case (start_pos, kind span) of
            (NONE, Command_Span _) => ranges (SOME (#1 (range span))) rest result
          | (SOME pos, Command_Span _) =>
              let
                val pos' = #1 (range span);
                val result' = Position.range (pos, pos') :: result;
              in ranges (SOME pos') rest result' end
          | _ => ranges start_pos rest result);
  in ranges NONE spans [] end;

end;
