(*  Title:      Pure/General/antiquote.ML
    Author:     Makarius

Antiquotations within plain text.
*)

signature ANTIQUOTE =
sig
  type control = {range: Position.range, name: string * Position.T, body: Symbol_Pos.T list}
  type antiq = {start: Position.T, stop: Position.T, range: Position.range, body: Symbol_Pos.T list}
  datatype 'a antiquote = Text of 'a | Control of control | Antiq of antiq
  val is_text: 'a antiquote -> bool
  val the_text: string -> 'a antiquote -> 'a
  type text_antiquote = Symbol_Pos.T list antiquote
  val text_antiquote_range: text_antiquote -> Position.range
  val text_range: text_antiquote list -> Position.range
  val split_lines: text_antiquote list -> text_antiquote list list
  val antiq_reports: 'a antiquote list -> Position.report list
  val update_reports: bool -> Position.T -> string list -> Position.report_text list
  val scan_control: control scanner
  val scan_antiq: antiq scanner
  val scan_antiquote: text_antiquote scanner
  val scan_antiquote_comments: text_antiquote scanner
  val parse_comments: Position.T -> Symbol_Pos.T list -> text_antiquote list
  val read_comments: Input.source -> text_antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

type control = {range: Position.range, name: string * Position.T, body: Symbol_Pos.T list};
type antiq = {start: Position.T, stop: Position.T, range: Position.range, body: Symbol_Pos.T list};
datatype 'a antiquote = Text of 'a | Control of control | Antiq of antiq;

val is_text = fn Text _ => true | _ => false;

fun the_text msg antiq =
  let fun err pos = error (msg ^ Position.here pos) in
    (case antiq of
      Text x => x
    | Control {range, ...} => err (#1 range)
    | Antiq {range, ...} => err (#1 range))
  end;

type text_antiquote = Symbol_Pos.T list antiquote;

fun text_antiquote_range (Text ss) = Symbol_Pos.range ss
  | text_antiquote_range (Control {range, ...}) = range
  | text_antiquote_range (Antiq {range, ...}) = range;

fun text_range ants =
  if null ants then Position.no_range
  else
    Position.range (#1 (text_antiquote_range (hd ants)), #2 (text_antiquote_range (List.last ants)));


(* split lines *)

fun split_lines input =
  let
    fun add a (line, lines) = (a :: line, lines);
    fun flush (line, lines) = ([], rev line :: lines);
    fun split (a as Text ss) =
          (case chop_prefix (fn ("\n", _) => false | _ => true) ss of
            ([], []) => I
          | (_, []) => add a
          | ([], _ :: rest) => flush #> split (Text rest)
          | (prefix, _ :: rest) => add (Text prefix) #> flush #> split (Text rest))
      | split a = add a;
  in if null input then [] else rev (#2 (flush (fold split input ([], [])))) end;


(* reports *)

fun antiq_reports ants = ants |> maps
  (fn Text _ => []
    | Control {range = (pos, _), ...} => [(pos, Markup.antiquoted)]
    | Antiq {start, stop, range = (pos, _), ...} =>
        [(start, Markup.antiquote),
         (stop, Markup.antiquote),
         (pos, Markup.antiquoted),
         (pos, Markup.language_antiquotation)]);


(* update *)

fun update_reports embedded pos src =
  let
    val n = length src;
    val no_arg = n = 1;
    val embedded_arg = n = 2 andalso embedded;
    val control =
      (case src of
        name :: _ =>
          if Symbol.is_ascii_identifier name andalso name <> "cartouche" andalso
            (no_arg orelse embedded_arg)
          then SOME (Symbol.control_prefix ^ name ^ Symbol.control_suffix)
          else NONE
      | [] => NONE);
    val arg = if embedded_arg then cartouche (nth src 1) else "";
  in
    (case control of
      SOME sym => [((pos, Markup.update), sym ^ arg)]
    | NONE => [])
  end;



(* scan *)

open Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val scan_nl = Scan.one (fn (s, _) => s = "\n") >> single;
val scan_nl_opt = Scan.optional scan_nl [];

val scan_plain_txt =
  Scan.many1 (fn (s, _) =>
    not (Comment.is_symbol s) andalso
    not (Symbol.is_control s) andalso
    s <> Symbol.open_ andalso
    s <> "@" andalso
    s <> "\n" andalso
    Symbol.not_eof s) ||
  Scan.one (Comment.is_symbol o Symbol_Pos.symbol) >> single ||
  $$$ "@" --| Scan.ahead (~$$ "{");

val scan_text =
  scan_nl || Scan.repeats1 scan_plain_txt @@@ scan_nl_opt;

val scan_text_comments =
  scan_nl || Scan.repeats1 (Comment.scan_inner >> #2 || scan_plain_txt) @@@ scan_nl_opt;

val scan_antiq_body =
  Scan.trace (Symbol_Pos.scan_string_qq err_prefix || Symbol_Pos.scan_string_bq err_prefix) >> #2 ||
  Symbol_Pos.scan_cartouche err_prefix ||
  Comment.scan_inner --
    Symbol_Pos.!!! (fn () => err_prefix ^ "bad formal comment in antiquote body") Scan.fail
    >> K [] ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.not_eof s) >> single;

fun control_name sym = (case Symbol.decode sym of Symbol.Control name => name);

in

val scan_control =
  Scan.option (Scan.one (Symbol.is_control o Symbol_Pos.symbol)) --
  Symbol_Pos.scan_cartouche err_prefix >>
    (fn (opt_control, body) =>
      let
        val (name, range) =
          (case opt_control of
            SOME (sym, pos) => ((control_name sym, pos), Symbol_Pos.range ((sym, pos) :: body))
          | NONE => (("cartouche", #2 (hd body)), Symbol_Pos.range body));
      in {name = name, range = range, body = body} end) ||
  Scan.one (Symbol.is_control o Symbol_Pos.symbol) >>
    (fn (sym, pos) =>
      {name = (control_name sym, pos), range = Symbol_Pos.range [(sym, pos)], body = []});

val scan_antiq =
  Symbol_Pos.scan_pos -- ($$ "@" |-- $$ "{" |-- Symbol_Pos.scan_pos --
    Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing brace")
      (Scan.repeats scan_antiq_body -- Symbol_Pos.scan_pos -- ($$ "}" |-- Symbol_Pos.scan_pos))) >>
    (fn (pos1, (pos2, ((body, pos3), pos4))) =>
      {start = Position.range_position (pos1, pos2),
       stop = Position.range_position (pos3, pos4),
       range = Position.range (pos1, pos4),
       body = body});

val scan_antiquote =
  scan_text >> Text || scan_control >> Control || scan_antiq >> Antiq;

val scan_antiquote_comments =
  scan_text_comments >> Text || scan_control >> Control || scan_antiq >> Antiq;

end;


(* parse and read (with formal comments) *)

fun parse_comments pos syms =
  (case Scan.read Symbol_Pos.stopper (Scan.repeat scan_antiquote_comments) syms of
    SOME ants => ants
  | NONE => error ("Malformed quotation/antiquotation source" ^ Position.here pos));

fun read_comments source =
  let
    val ants = parse_comments (Input.pos_of source) (Input.source_explode source);
    val _ = Position.reports (antiq_reports ants);
  in ants end;

end;
