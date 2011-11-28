(*  Title:      Pure/Thy/thy_syntax.ML
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*)

signature THY_SYNTAX =
sig
  val token_source: Scan.lexicon * Scan.lexicon -> Position.T -> (string, 'a) Source.source ->
    (Token.T, (Symbol_Pos.T, Position.T * (Symbol.symbol, (string, 'a)
      Source.source) Source.source) Source.source) Source.source
  val parse_tokens: Scan.lexicon * Scan.lexicon -> Position.T -> string -> Token.T list
  val present_token: Token.T -> Output.output
  val reports_of_token: Token.T -> Position.report list
  datatype span_kind = Command of string | Ignored | Malformed
  type span
  val span_kind: span -> span_kind
  val span_content: span -> Token.T list
  val span_source: (Token.T, 'a) Source.source -> (span, (Token.T, 'a) Source.source) Source.source
  val parse_spans: Scan.lexicon * Scan.lexicon -> Position.T -> string -> span list
  val present_span: span -> Output.output
  type element = {head: span, proof: span list, proper_proof: bool}
  val element_source: (span, 'a) Source.source ->
    (element, (span, 'a) Source.source) Source.source
end;

structure Thy_Syntax: THY_SYNTAX =
struct

(** tokens **)

(* parse *)

fun token_source lexs pos =
  Symbol.source #> Token.source {do_recover = SOME false} (K lexs) pos;

fun parse_tokens lexs pos =
  Source.of_string #> token_source lexs pos #> Source.exhaust;


(* present *)

local

val token_kind_markup =
 fn Token.Command       => Isabelle_Markup.command
  | Token.Keyword       => Isabelle_Markup.keyword
  | Token.Ident         => Markup.empty
  | Token.LongIdent     => Markup.empty
  | Token.SymIdent      => Markup.empty
  | Token.Var           => Isabelle_Markup.var
  | Token.TypeIdent     => Isabelle_Markup.tfree
  | Token.TypeVar       => Isabelle_Markup.tvar
  | Token.Nat           => Markup.empty
  | Token.Float         => Markup.empty
  | Token.String        => Isabelle_Markup.string
  | Token.AltString     => Isabelle_Markup.altstring
  | Token.Verbatim      => Isabelle_Markup.verbatim
  | Token.Space         => Markup.empty
  | Token.Comment       => Isabelle_Markup.comment
  | Token.InternalValue => Markup.empty
  | Token.Error _       => Isabelle_Markup.malformed
  | Token.Sync          => Isabelle_Markup.control
  | Token.EOF           => Isabelle_Markup.control;

fun token_markup tok =
  if Token.keyword_with (not o Lexicon.is_ascii_identifier) tok then Isabelle_Markup.operator
  else
    let
      val kind = Token.kind_of tok;
      val props =
        if kind = Token.Command
        then Markup.properties [(Markup.nameN, Token.content_of tok)]
        else I;
    in props (token_kind_markup kind) end;

fun reports_of_symbol (sym, pos) =
  if Symbol.is_malformed sym then [(pos, Isabelle_Markup.malformed)] else [];

in

fun present_token tok =
  Markup.enclose (token_markup tok) (Output.output (Token.unparse tok));

fun reports_of_token tok =
  (Token.position_of tok, token_markup tok) ::
    maps reports_of_symbol (Symbol_Pos.explode (Token.source_position_of tok));

end;



(** spans **)

(* type span *)

datatype span_kind = Command of string | Ignored | Malformed;
datatype span = Span of span_kind * Token.T list;

fun span_kind (Span (k, _)) = k;
fun span_content (Span (_, toks)) = toks;


(* parse *)

local

val whitespace = Scan.many (not o Token.is_proper);
val whitespace1 = Scan.many1 (not o Token.is_proper);

val body = Scan.unless (whitespace -- Scan.ahead (Parse.command || Parse.eof)) Parse.not_eof;

val span =
  Scan.ahead Parse.command -- Parse.not_eof -- Scan.repeat body
    >> (fn ((name, c), bs) => Span (Command name, c :: bs)) ||
  whitespace1 >> (fn toks => Span (Ignored, toks)) ||
  Scan.repeat1 body >> (fn toks => Span (Malformed, toks));

in

fun span_source src = Source.source Token.stopper (Scan.bulk span) NONE src;

end;

fun parse_spans lexs pos str =
  Source.of_string str
  |> token_source lexs pos
  |> span_source
  |> Source.exhaust;


(* present *)

local

fun kind_markup (Command name) = Isabelle_Markup.command_span name
  | kind_markup Ignored = Isabelle_Markup.ignored_span
  | kind_markup Malformed = Isabelle_Markup.malformed_span;

in

fun present_span span =
  Markup.enclose (kind_markup (span_kind span)) (implode (map present_token (span_content span)));

end;



(** specification elements: commands with optional proof **)

type element = {head: span, proof: span list, proper_proof: bool};

fun make_element head proof proper_proof =
  {head = head, proof = proof, proper_proof = proper_proof};


(* scanning spans *)

val eof = Span (Command "", []);

fun is_eof (Span (Command "", _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper = Scan.stopper (K eof) is_eof;


(* element_source *)

local

fun command_with pred = Scan.one (fn (Span (Command name, _)) => pred name | _ => false);

val proof = Scan.pass 1 (Scan.repeat (Scan.depend (fn d =>
  if d <= 0 then Scan.fail
  else
    command_with Keyword.is_qed_global >> pair ~1 ||
    command_with Keyword.is_proof_goal >> pair (d + 1) ||
    (if d = 0 then Scan.fail else command_with Keyword.is_qed >> pair (d - 1)) ||
    Scan.unless (command_with Keyword.is_theory) (Scan.one not_eof) >> pair d)) -- Scan.state);

val element =
  command_with Keyword.is_theory_goal -- proof
    >> (fn (a, (bs, d)) => make_element a bs (d >= 0)) ||
  Scan.one not_eof >> (fn a => make_element a [] true);

in

fun element_source src = Source.source stopper (Scan.bulk element) NONE src;

end;

end;
