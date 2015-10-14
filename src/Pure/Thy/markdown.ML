(*  Title:      Pure/Thy/markdown.ML
    Author:     Makarius

Minimal support for Markdown documents (see also http://commonmark.org).
*)

signature MARKDOWN =
sig
  datatype kind = Itemize | Enumerate | Description
  type line
  val line_content: line -> Antiquote.text_antiquote list
  datatype block = Paragraph of line list | List of kind * block list list
  val read_document: Input.source -> block list
end;

structure Markdown: MARKDOWN =
struct

(* document structure *)

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

datatype block = Paragraph of line list | List of kind * block list list;


(* make line *)

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

val scan_prefix =
  (Scan.many is_space >> length) --
  Scan.option
    ((Symbol_Pos.$$ "\<^item>" >> K Itemize ||
      Symbol_Pos.$$ "\<^enum>" >> K Enumerate ||
      Symbol_Pos.$$ "\<^descr>" >> K Description) -- Symbol_Pos.scan_pos);

fun scan_line (Antiquote.Text ss :: _) =
      the_default (0, NONE) (Scan.read Symbol_Pos.stopper scan_prefix ss)
  | scan_line _ = (0, NONE);

in

fun make_line content =
  let
    val _ = check_blanks content;
    val (indent, marker) = scan_line content;
  in Line {content = content, is_empty = is_empty content, indent = indent, marker = marker} end;

end;


(* make blocks *)

fun make_blocks spans = map Paragraph spans;


(* read document *)

local

val eof =
  Line {content = [Antiquote.Text [(Symbol.eof, Position.none)]],
    is_empty = false, indent = 0, marker = NONE};
val stopper = Scan.stopper (K eof) (fn line => line = eof);

fun plain_line line =
  not (line_is_empty line) andalso is_none (line_marker line) andalso line <> eof;

val parse_span =
  Scan.many1 plain_line || Scan.one (is_some o line_marker) -- Scan.many plain_line >> op ::;

val parse_document =
  parse_span ::: Scan.repeat (Scan.one line_is_empty |-- parse_span) >> make_blocks;

val parse_documents =
  (Scan.many line_is_empty |-- parse_document) :::
    (Scan.repeat (Scan.many1 line_is_empty |-- parse_document) --| Scan.many line_is_empty)
  >> flat;

in

val read_document =
  Antiquote.read #> Antiquote.split_lines #> map make_line #>
  Scan.read stopper parse_documents #> the_default [];

end;

end;
