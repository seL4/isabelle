(*  Title:      Pure/Thy/markdown.ML
    Author:     Makarius

Minimal support for Markdown documents (see also http://commonmark.org)
that consist only of paragraphs and (nested) lists:

  * list items start with marker \<^item> (itemize), \<^enum> (enumerate), \<^descr> (description)
  * adjacent list items with same indentation and same marker are grouped
    into a single list
  * singleton blank lines separate paragraphs
  * multiple blank lines escape from the current list hierarchy

Notable differences to official Markdown:

  * indentation of list items needs to match exactly
  * indentation is unlimited (Markdown interprets 4 spaces as block quote)
  * list items always consist of paragraphs -- no notion of "tight" list
*)

signature MARKDOWN =
sig
  datatype kind = Itemize | Enumerate | Description
  val print_kind: kind -> string
  type marker = {indent: int, kind: kind}
  type line
  val line_content: line -> Antiquote.text_antiquote list
  val make_line: Antiquote.text_antiquote list -> line
  val empty_line: line
  datatype block = Paragraph of line list | List of marker * block list
  val read_lines: line list -> block list
  val read: Input.source -> block list
  val reports: block list -> Position.report list
end;

structure Markdown: MARKDOWN =
struct

(* document lines *)

datatype kind = Itemize | Enumerate | Description;

fun print_kind Itemize = "itemize"
  | print_kind Enumerate = "enumerate"
  | print_kind Description = "description";

type marker = {indent: int, kind: kind};

datatype line =
  Line of
   {content: Antiquote.text_antiquote list,
    is_empty: bool,
    marker: (marker * Position.T) option};

val eof_line =
  Line {content = [Antiquote.Text [(Symbol.eof, Position.none)]],
    is_empty = false, marker = NONE};

fun line_content (Line {content, ...}) = content;
fun line_is_empty (Line {is_empty, ...}) = is_empty;
fun line_marker (Line {marker, ...}) = marker;


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
  Scan.many is_space -- Symbol_Pos.scan_pos --
  (Symbol_Pos.$$ "\<^item>" >> K Itemize ||
   Symbol_Pos.$$ "\<^enum>" >> K Enumerate ||
   Symbol_Pos.$$ "\<^descr>" >> K Description)
  >> (fn ((spaces, pos), kind) => ({indent = length spaces, kind = kind}, pos));

fun read_marker (Antiquote.Text ss :: _) =
      #1 (Scan.finite Symbol_Pos.stopper (Scan.option scan_marker) ss)
  | read_marker _ = NONE;

in

fun make_line content =
  let
    val _ = check_blanks content;
    val marker = read_marker content;
  in Line {content = content, is_empty = is_empty content, marker = marker} end;

val empty_line = make_line [];

end;


(* document blocks *)

datatype block = Paragraph of line list | List of marker * block list;

fun block_lines (Paragraph lines) = lines
  | block_lines (List (_, blocks)) = maps block_lines blocks;


fun add_span (opt_marker, body) document =
  (case (opt_marker, document) of
    (SOME marker, (list as List (list_marker, list_body)) :: rest) =>
      if marker = list_marker then
        List (list_marker, body @ list_body) :: rest
      else if #indent marker < #indent list_marker then
        List (marker, body @ [list]) :: rest
      else
        List (marker, body) :: document
  | (SOME marker, _) => List (marker, body) :: document
  | (NONE, _) => body @ document);


(* read document *)

local

fun plain_line line =
  not (line_is_empty line) andalso is_none (line_marker line) andalso line <> eof_line;

val parse_paragraph = Scan.many1 plain_line >> Paragraph;

val parse_span =
  parse_paragraph >> (fn par => (NONE, [par])) ||
  Scan.one (is_some o line_marker) -- Scan.many plain_line --
    Scan.repeat (Scan.one line_is_empty |-- parse_paragraph) >>
      (fn ((line, lines), pars) =>
        (Option.map #1 (line_marker line), Paragraph (line :: lines) :: pars));

val parse_document =
  parse_span ::: Scan.repeat (Scan.option (Scan.one line_is_empty) |-- parse_span)
    >> (fn spans => fold_rev add_span spans []);

in

val read_lines =
  Scan.read (Scan.stopper (K eof_line) (fn line => line = eof_line))
    (Scan.repeat (Scan.many line_is_empty |-- parse_document) --| Scan.many line_is_empty) #>
  the_default [] #> flat;

end;

val read = Antiquote.read #> Antiquote.split_lines #> map make_line #> read_lines;


(* PIDE reports *)

local

fun line_reports depth (Line {marker = SOME (_, pos), ...}) =
      cons (pos, Markup.markdown_item depth)
  | line_reports _ _ = I;

val lines_pos = #1 o Antiquote.range o maps line_content;

fun block_reports depth (Paragraph lines) =
      cons (lines_pos lines, Markup.markdown_paragraph) #>
      fold (line_reports depth) lines
  | block_reports depth (List ({kind, ...}, body)) =
      cons (lines_pos (maps block_lines body), Markup.markdown_list (print_kind kind)) #>
      fold (block_reports (depth + 1)) body;

in

fun reports blocks =
  filter (Position.is_reported o #1) (fold (block_reports 0) blocks []);

end;

end;
