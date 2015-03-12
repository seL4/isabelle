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
  val resolve_files: Keyword.keywords ->
    (string -> Path.T * Position.T -> Token.file Exn.result list) -> span -> span
end;

structure Command_Span: COMMAND_SPAN =
struct

datatype kind = Command_Span of string * Position.T | Ignored_Span | Malformed_Span;
datatype span = Span of kind * Token.T list;

fun kind (Span (k, _)) = k;
fun content (Span (_, toks)) = toks;


(* resolve inlined files *)

local

fun clean ((t1, i1) :: (t2, i2) :: rest) =
      if Token.keyword_with (fn s => s = "%" orelse s = "--") t1 then clean rest
      else (t1, i1) :: clean ((t2, i2) :: rest)
  | clean toks = toks;

fun clean_tokens tokens =
  clean (filter (fn (t, _) => Token.is_proper t) (tokens ~~ (0 upto length tokens - 1)));

fun find_file ((tok, _) :: toks) =
      if Token.is_command tok then
        toks |> get_first (fn (t, i) =>
          if Token.is_name t then
            SOME ((Path.explode (Token.content_of t), Token.pos_of t), i)
              handle ERROR msg => error (msg ^ Position.here (Token.pos_of t))
          else NONE)
      else NONE
  | find_file [] = NONE;

in

fun resolve_files keywords read_files span =
  (case span of
    Span (Command_Span (cmd, pos), toks) =>
      if Keyword.is_theory_load keywords cmd then
        (case find_file (clean_tokens toks) of
          NONE => error ("Bad file argument of command " ^ quote cmd ^ Position.here pos)
        | SOME (path, i) =>
            let
              val toks' = toks |> map_index (fn (j, tok) =>
                if i = j then Token.put_files (read_files cmd path) tok
                else tok);
            in Span (Command_Span (cmd, pos), toks') end)
      else span
  | _ => span);

end;

end;

