(*  Title:	Pure/Thy/thy_scan.ML
    ID:		$Id$
    Author:	Markus Wenzel, TU Muenchen

Lexer for the outer Isabelle syntax.

TODO:
  - old vs. new: interpreted strings, no 'ML', var!?;
*)

signature THY_SCAN =
sig
  datatype token_kind =
    Keyword | Ident | LongIdent | Var | TypeVar | Nat | String | Verbatim | Ignore | EOF
  val name_of_kind: token_kind -> string
  val tokenize: Scan.lexicon -> string -> (token_kind * string * int) list
end;

structure ThyScan: THY_SCAN =
struct


(** token kinds **)

datatype token_kind =
  Keyword | Ident | LongIdent | Var | TypeVar | Nat | String | Verbatim | Ignore | EOF;

fun name_of_kind Keyword = "keyword"
  | name_of_kind Ident = "identifier"
  | name_of_kind LongIdent = "long identifier"
  | name_of_kind Var = "schematic variable"
  | name_of_kind TypeVar = "type variable"
  | name_of_kind Nat = "natural number"
  | name_of_kind String = "string"
  | name_of_kind Verbatim = "verbatim text"
  | name_of_kind Ignore = "ignore"
  | name_of_kind EOF = "end-of-file";



(** scanners **)

(* diagnostics *)

fun lex_err None msg = "Outer lexical error: " ^ msg
  | lex_err (Some n) msg = "Outer lexical error on line " ^ string_of_int n ^ ": " ^ msg;


(* line numbering *)

val incr = apsome (fn n:int => n + 1);

fun incr_line scan = Scan.depend (fn n => scan >> pair (incr n));
val keep_line = Scan.lift;

val scan_blank =
  incr_line ($$ "\n") ||
  keep_line (Scan.one Symbol.is_blank);


(* scan ML-style strings *)

val scan_ctrl =
  $$ "^" ^^ Scan.one (fn c => Symbol.is_ascii c andalso ord c >= 64 andalso ord c <= 95);

val scan_dig = Scan.one Symbol.is_digit;

val scan_esc =
  keep_line ($$ "\\") ^^ !! (fn (n, _) => lex_err n "bad escape sequence in string")
    (keep_line ($$ "n" || $$ "t" || $$ "\"" || $$ "\\" ||
      scan_ctrl || scan_dig ^^ scan_dig ^^ scan_dig) ||
      (Scan.repeat1 scan_blank >> implode) ^^ keep_line ($$ "\\"));

val scan_str =
  scan_esc ||
  scan_blank >> K " " ||
  keep_line (Scan.one (not_equal "\"" andf Symbol.not_eof));

val scan_string =
  keep_line ($$ "\"") ^^
  !! (fn (n, _) => lex_err n "missing quote at end of string")
    ((Scan.repeat scan_str >> implode) ^^ keep_line ($$ "\""));


(* scan verbatim text *)

val scan_verb =
  scan_blank ||
  keep_line ($$ "|" --| Scan.ahead (Scan.one (not_equal "}"))) ||
  keep_line (Scan.one (not_equal "|" andf Symbol.not_eof));

val scan_verbatim =
  keep_line ($$ "{" -- $$ "|") |--
  !! (fn (n, _) => lex_err n "missing end of verbatim text")
    ((Scan.repeat scan_verb >> implode) --| keep_line ($$ "|" -- $$ "}"));


(* scan nested comments *)

val scan_cmt =
  Scan.lift scan_blank ||
  Scan.depend (fn d => keep_line ($$ "(" ^^ $$ "*") >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => keep_line ($$ "*" ^^ $$ ")") >> pair (d - 1)) ||
  Scan.lift (keep_line ($$ "*" --| Scan.ahead (Scan.one (not_equal ")")))) ||
  Scan.lift (keep_line (Scan.one (not_equal "*" andf Symbol.not_eof)));

val scan_comment =
  keep_line ($$ "(" -- $$ "*") |--
  !! (fn (n, _) => lex_err n "missing end of comment")
    (Scan.pass 0 (Scan.repeat scan_cmt) |-- keep_line ($$ "*" -- $$ ")") >> K "");


(* scan token *)

fun token k None x = (k, x, 0)
  | token k (Some n) x = (k, x, n);

fun scan_tok lex (n, cs) =
 (scan_string >> token String n ||
  scan_verbatim >> token Verbatim n ||
  Scan.repeat1 scan_blank >> (token Ignore n o implode) ||
  scan_comment >> token Ignore n ||
  keep_line (Scan.max (fn ((_, x, _), (_, x', _)) => x <= x')
    (Scan.literal lex >> (token Keyword n o implode))
    (Syntax.scan_longid >> token LongIdent n ||
      Syntax.scan_id >> token Ident n ||
      Syntax.scan_var >> token Var n ||
      Syntax.scan_tid >> token TypeVar n ||
      Syntax.scan_nat >> token Nat n))) (n, cs);

val scan_rest = Scan.any Symbol.not_eof >> implode;

fun scan_token lex x =
  (case scan_tok lex x of
    ((Keyword, "ML", n), x') => (keep_line scan_rest >> token Verbatim (Some n)) x'
  | tok_x' => tok_x');


(* tokenize *)

fun tokenize lex str =
  let
    val chs = explode str;	(*sic!*)
    val scan_toks = Scan.repeat (scan_token lex);
    val ignore = fn (Ignore, _, _) => true | _ => false;
  in
    (case Scan.error (Scan.finite' Symbol.eof scan_toks) (Some 1, chs) of
      (toks, (n, [])) => filter_out ignore toks @ [token EOF n "end-of-file"]
    | (_, (n, cs)) => error (lex_err n ("Bad input " ^ quote (beginning cs))))
  end;


end;
