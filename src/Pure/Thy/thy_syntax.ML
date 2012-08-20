(*  Title:      Pure/Thy/thy_syntax.ML
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*)

signature THY_SYNTAX =
sig
  val parse_tokens: Scan.lexicon * Scan.lexicon -> Position.T -> string -> Token.T list
  val reports_of_tokens: Token.T list -> bool * (Position.report * string) list
  val present_token: Token.T -> Output.output
  datatype span_kind = Command of string | Ignored | Malformed
  type span
  val span_kind: span -> span_kind
  val span_content: span -> Token.T list
  val present_span: span -> Output.output
  val parse_spans: Token.T list -> span list
  type element = {head: span, proof: span list, proper_proof: bool}
  val parse_elements: span list -> element list
end;

structure Thy_Syntax: THY_SYNTAX =
struct

(** tokens **)

(* parse *)

fun parse_tokens lexs pos =
  Source.of_string #>
  Symbol.source #>
  Token.source {do_recover = SOME false} (K lexs) pos #>
  Source.exhaust;


(* present *)

local

val token_kind_markup =
 fn Token.Command       => (Isabelle_Markup.command, "")
  | Token.Keyword       => (Isabelle_Markup.keyword, "")
  | Token.Ident         => (Markup.empty, "")
  | Token.LongIdent     => (Markup.empty, "")
  | Token.SymIdent      => (Markup.empty, "")
  | Token.Var           => (Isabelle_Markup.var, "")
  | Token.TypeIdent     => (Isabelle_Markup.tfree, "")
  | Token.TypeVar       => (Isabelle_Markup.tvar, "")
  | Token.Nat           => (Markup.empty, "")
  | Token.Float         => (Markup.empty, "")
  | Token.String        => (Isabelle_Markup.string, "")
  | Token.AltString     => (Isabelle_Markup.altstring, "")
  | Token.Verbatim      => (Isabelle_Markup.verbatim, "")
  | Token.Space         => (Markup.empty, "")
  | Token.Comment       => (Isabelle_Markup.comment, "")
  | Token.InternalValue => (Markup.empty, "")
  | Token.Error msg     => (Isabelle_Markup.bad, msg)
  | Token.Sync          => (Isabelle_Markup.control, "")
  | Token.EOF           => (Isabelle_Markup.control, "");

fun token_markup tok =
  if Token.keyword_with (not o Lexicon.is_ascii_identifier) tok
  then (Isabelle_Markup.operator, "")
  else
    let
      val kind = Token.kind_of tok;
      val props =
        if kind = Token.Command
        then Markup.properties [(Markup.nameN, Token.content_of tok)]
        else I;
      val (markup, txt) = token_kind_markup kind;
    in (props markup, txt) end;

fun reports_of_token tok =
  let
    val malformed_symbols =
      Symbol_Pos.explode (Token.source_position_of tok)
      |> map_filter (fn (sym, pos) =>
          if Symbol.is_malformed sym
          then SOME ((pos, Isabelle_Markup.bad), "Malformed symbolic character") else NONE);
    val is_malformed = Token.is_error tok orelse not (null malformed_symbols);
    val (markup, txt) = token_markup tok;
    val reports = ((Token.position_of tok, markup), txt) :: malformed_symbols;
  in (is_malformed, reports) end;

in

fun reports_of_tokens toks =
  let val results = map reports_of_token toks
  in (exists fst results, maps snd results) end;

fun present_token tok =
  Markup.enclose (fst (token_markup tok)) (Output.output (Token.unparse tok));

end;



(** spans **)

(* type span *)

datatype span_kind = Command of string | Ignored | Malformed;
datatype span = Span of span_kind * Token.T list;

fun span_kind (Span (k, _)) = k;
fun span_content (Span (_, toks)) = toks;

val present_span = implode o map present_token o span_content;


(* parse *)

local

fun make_span toks =
  if not (null toks) andalso Token.is_command (hd toks) then
    Span (Command (Token.content_of (hd toks)), toks)
  else if forall (not o Token.is_proper) toks then Span (Ignored, toks)
  else Span (Malformed, toks);

fun flush (result, span) = if null span then (result, span) else (rev span :: result, []);

in

fun parse_spans toks =
  fold (fn tok => Token.is_command tok ? flush #> apsnd (cons tok)) toks ([], [])
  |> flush
  |> #1 |> rev |> map make_span;

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


(* parse *)

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

val parse_elements =
  Source.of_list #>
  Source.source stopper (Scan.bulk element) NONE #>
  Source.exhaust;

end;

end;
