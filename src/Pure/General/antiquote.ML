(*  Title:      Pure/General/antiquote.ML
    Author:     Makarius

Antiquotations within plain text.
*)

signature ANTIQUOTE =
sig
  type antiq = Symbol_Pos.T list * {start: Position.T, stop: Position.T, range: Position.range}
  datatype 'a antiquote = Text of 'a | Antiq of antiq
  type text_antiquote = Symbol_Pos.T list antiquote
  val split_lines: text_antiquote list -> text_antiquote list list
  val antiq_reports: antiq -> Position.report list
  val antiquote_reports: ('a -> Position.report_text list) ->
    'a antiquote list -> Position.report_text list
  val scan_antiq: Symbol_Pos.T list -> antiq * Symbol_Pos.T list
  val scan_antiquote: Symbol_Pos.T list -> text_antiquote * Symbol_Pos.T list
  val read: Input.source -> text_antiquote list
end;

structure Antiquote: ANTIQUOTE =
struct

(* datatype antiquote *)

type antiq = Symbol_Pos.T list * {start: Position.T, stop: Position.T, range: Position.range};
datatype 'a antiquote = Text of 'a | Antiq of antiq;

type text_antiquote = Symbol_Pos.T list antiquote;


(* split lines *)

fun split_lines input =
  let
    fun add a (line, lines) = (a :: line, lines);
    fun flush (line, lines) = ([], rev line :: lines);
    fun split (a as Text ss) =
          (case take_prefix (fn ("\n", _) => false | _ => true) ss of
            ([], []) => I
          | (_, []) => add a
          | ([], _ :: rest) => flush #> split (Text rest)
          | (prefix, _ :: rest) => add (Text prefix) #> flush #> split (Text rest))
      | split a = add a;
  in if null input then [] else rev (#2 (flush (fold split input ([], [])))) end;


(* reports *)

fun antiq_reports ((_, {start, stop, range = (pos, _)}): antiq) =
  [(start, Markup.antiquote), (stop, Markup.antiquote),
   (pos, Markup.antiquoted), (pos, Markup.language_antiquotation)];

fun antiquote_reports text =
  maps (fn Text x => text x | Antiq antiq => map (rpair "") (antiq_reports antiq));


(* scan *)

open Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val scan_txt =
  Scan.repeat1 ($$$ "@" --| Scan.ahead (~$$ "{") ||
    Scan.many1 (fn (s, _) => s <> "@" andalso Symbol.not_eof s)) >> flat;

val scan_antiq_body =
  Scan.trace (Symbol_Pos.scan_string_qq err_prefix || Symbol_Pos.scan_string_bq err_prefix) >> #2 ||
  Scan.trace (Symbol_Pos.scan_cartouche err_prefix) >> #2 ||
  Scan.one (fn (s, _) => s <> "}" andalso Symbol.not_eof s) >> single;

in

val scan_antiq =
  Symbol_Pos.scan_pos -- ($$ "@" |-- $$ "{" |-- Symbol_Pos.scan_pos --
    Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing brace")
      (Scan.repeat scan_antiq_body -- Symbol_Pos.scan_pos -- ($$ "}" |-- Symbol_Pos.scan_pos)))
  >> (fn (pos1, (pos2, ((body, pos3), pos4))) =>
      (flat body,
        {start = Position.set_range (pos1, pos2),
         stop = Position.set_range (pos3, pos4),
         range = Position.range pos1 pos4}));

val scan_antiquote = scan_antiq >> Antiq || scan_txt >> Text;

end;


(* read *)

fun read source =
  (case Scan.read Symbol_Pos.stopper (Scan.repeat scan_antiquote) (Input.source_explode source) of
    SOME xs => (Position.reports_text (antiquote_reports (K []) xs); xs)
  | NONE =>
      error ("Malformed quotation/antiquotation source" ^ Position.here (Input.pos_of source)));

end;
