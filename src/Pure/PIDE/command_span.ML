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
  val resolve_files: (string -> Path.T * Position.T -> Token.file Exn.result list) -> span -> span
end;

structure Command_Span: COMMAND_SPAN =
struct

datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span;
datatype span = Span of kind * Token.T list;

fun kind (Span (k, _)) = k;
fun content (Span (_, toks)) = toks;


(* resolve inlined files *)

local

fun clean ((i1, t1) :: (i2, t2) :: toks) =
      if Token.keyword_with (fn s => s = "%" orelse s = "--") t1 then clean toks
      else (i1, t1) :: clean ((i2, t2) :: toks)
  | clean toks = toks;

fun clean_tokens toks =
  ((0 upto length toks - 1) ~~ toks)
  |> filter (fn (_, tok) => Token.is_proper tok)
  |> clean;

fun find_file ((_, tok) :: toks) =
      if Token.is_command tok then
        toks |> get_first (fn (i, tok) =>
          if Token.is_name tok then
            SOME (i, (Path.explode (Token.content_of tok), Token.pos_of tok))
              handle ERROR msg => error (msg ^ Position.here (Token.pos_of tok))
          else NONE)
      else NONE
  | find_file [] = NONE;

in

fun resolve_files read_files span =
  (case span of
    Span (Command_Span (cmd, pos), toks) =>
      if Keyword.is_theory_load cmd then
        (case find_file (clean_tokens toks) of
          NONE => error ("Bad file argument of command " ^ quote cmd ^ Position.here pos)
        | SOME (i, path) =>
            let
              val toks' = toks |> map_index (fn (j, tok) =>
                if i = j then Token.put_files (read_files cmd path) tok
                else tok);
            in Span (Command_Span (cmd, pos), toks') end)
      else span
  | _ => span);

end;

end;

