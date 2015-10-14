(*  Title:      Pure/Thy/markdown.ML
    Author:     Makarius

Minimal support for Markdown documents (see also http://commonmark.org).
*)

signature MARKDOWN =
sig
  type line
  val read: Input.source -> line list list
end;

structure Markdown: MARKDOWN =
struct

(* line with optional item marker *)

datatype kind = Itemize | Enumerate | Description;

datatype line =
  Line of
   {content: Antiquote.text_antiquote list,
    is_empty: bool,
    indent: int,
    marker: (kind * Position.T) option};

fun line_content (Line {content, ...}) = content;
fun line_is_empty (Line {is_empty, ...}) = is_empty;
fun line_indent (Line {indent, ...}) = indent;
fun line_marker (Line {marker, ...}) = marker;

local

fun bad_blank ((s, _): Symbol_Pos.T) = Symbol.is_ascii_blank s andalso s <> Symbol.space;
val bad_blanks = maps (fn Antiquote.Text ss => filter bad_blank ss | _ => []);

fun check_blanks content =
  (case bad_blanks content of
    [] => ()
  | (c, pos) :: _ =>
      error ("Bad blank character " ^ quote (ML_Syntax.print_char c) ^ Position.here pos));

fun is_space ((s, _): Symbol_Pos.T) = s = Symbol.space;
val is_empty = forall (fn Antiquote.Text ss => forall is_space ss | _ => false);

fun line_kind (Antiquote.Text ss :: _) =
      let
        val (spaces, rest) = take_prefix is_space ss;
        fun make_marker kind =
          (case rest of
            [(_, pos)] => (kind, pos)
          | (_, pos) :: (" ", _) :: _ => (kind, pos)
          | (_, pos) :: _ => error ("Missing space after item marker" ^ Position.here pos));
        val marker =
          (case rest of
            ("\<^item>", _) :: _ => SOME (make_marker Itemize)
          | ("\<^enum>", _) :: _ => SOME (make_marker Enumerate)
          | ("\<^descr>", _) :: _ => SOME (make_marker Description)
          | _ => NONE);
      in (length spaces, marker) end
  | line_kind _ = (0, NONE);

in

fun make_line content =
  let
    val _ = check_blanks content;
    val (indent, marker) = line_kind content;
  in Line {content = content, is_empty = is_empty content, indent = indent, marker = marker} end;

end;


(* spans of related lines *)

local

val eof = make_line [Antiquote.Text [(Symbol.eof, Position.none)]];
val stopper = Scan.stopper (K eof) (fn line => line = eof);

fun item_line line = is_some (line_marker line);
fun plain_line line = is_none (line_marker line) andalso line <> eof;

val parse_span =
  Scan.one item_line -- Scan.many plain_line >> op :: ||
  Scan.many1 plain_line ||
  Scan.many1 line_is_empty;

in

fun read_spans lines =
  the_default [] (Scan.read stopper (Scan.repeat parse_span) lines);

end;


(* document structure *)

fun read input =
  Antiquote.read input
  |> Antiquote.split_lines
  |> map make_line
  |> read_spans;

end;
