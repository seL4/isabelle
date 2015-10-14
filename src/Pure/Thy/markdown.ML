(*  Title:      Pure/Thy/markdown.ML
    Author:     Makarius

Minimal support for Markdown documents (see also http://commonmark.org).
*)

signature MARKDOWN =
sig
  datatype kind = Itemize | Enumerate | Description
  type line
  val line_content: line -> Antiquote.text_antiquote list
  datatype block = Paragraph of line list | List of kind * block list
  val read_document: Input.source -> block list
end;

structure Markdown: MARKDOWN =
struct

(* document structure *)

datatype kind = Itemize | Enumerate | Description;
type marker = {indent: int, kind: kind, pos: Position.T};

datatype line =
  Line of
   {content: Antiquote.text_antiquote list,
    is_empty: bool,
    marker: marker option};

fun line_content (Line {content, ...}) = content;
fun line_is_empty (Line {is_empty, ...}) = is_empty;
fun line_marker (Line {marker, ...}) = marker;

datatype block = Paragraph of line list | List of kind * block list;


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

val scan_marker =
  Scan.many is_space --
    (Symbol_Pos.$$ "\<^item>" >> K Itemize ||
     Symbol_Pos.$$ "\<^enum>" >> K Enumerate ||
     Symbol_Pos.$$ "\<^descr>" >> K Description)
    -- Symbol_Pos.scan_pos
    >> (fn ((a, b), c) => ({indent = length a, kind = b, pos = c}: marker));

fun read_marker (Antiquote.Text ss :: _) =
      #1 (Scan.finite Symbol_Pos.stopper (Scan.option scan_marker) ss)
  | read_marker _ = NONE;

in

fun make_line content =
  let
    val _ = check_blanks content;
    val marker = read_marker content;
  in Line {content = content, is_empty = is_empty content, marker = marker} end;

end;


(* read document *)

local

val eof =
  Line {content = [Antiquote.Text [(Symbol.eof, Position.none)]],
    is_empty = false, marker = NONE};

val stopper = Scan.stopper (K eof) (fn line => line = eof);

fun plain_line line =
  not (line_is_empty line) andalso is_none (line_marker line) andalso line <> eof;

val parse_paragraph = Scan.many1 plain_line >> Paragraph;

val parse_span =
  parse_paragraph >> (fn par => (NONE, [par])) ||
  Scan.one (is_some o line_marker) -- Scan.many plain_line --
    Scan.repeat (Scan.one line_is_empty |-- parse_paragraph) >>
      (fn ((line, lines), pars) => ((line_marker line), Paragraph (line :: lines) :: pars));

val parse_document =
  parse_span ::: Scan.repeat (Scan.option (Scan.one line_is_empty) |-- parse_span) >> maps snd;

val parse_documents =
  Scan.repeat (Scan.many line_is_empty |-- parse_document) --| Scan.many line_is_empty >> flat;

in

val read_document =
  Antiquote.read #> Antiquote.split_lines #> map make_line #>
  Scan.read stopper parse_documents #> the_default [];

end;

end;
