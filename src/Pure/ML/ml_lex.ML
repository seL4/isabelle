(*  Title:      Pure/ML/ml_lex.ML
    ID:         $Id$
    Author:     Makarius

Lexical syntax for SML.
*)

signature ML_LEX =
sig
  datatype token_kind =
    Keyword | Ident | LongIdent | TypeVar | Selector | Word | Int | Real | Char | String |
    Space | Comment | Error of string | EOF
  eqtype token
  val str_of_kind: token_kind -> string
  val stopper: token * (token -> bool)
  val not_eof: token -> bool
  val kind_of: token -> token_kind
  val is_kind: token_kind -> token -> bool
  val is_proper: token -> bool
  val val_of: token -> string
  val !!! : string -> (int * 'a -> 'b) -> int * 'a -> 'b
  val keywords: string list
  val scan: int * string list -> token * (int * string list)
  val source: bool option -> (string, 'a) Source.source ->
    (token, int * (string, 'a) Source.source) Source.source
  val source_proper: (token, 'a) Source.source ->
    (token, (token, 'a) Source.source) Source.source
end;

structure ML_Lex: ML_LEX =
struct

(** tokens **)

(* datatype token *)

datatype token_kind =
  Keyword | Ident | LongIdent | TypeVar | Selector | Word | Int | Real | Char | String |
  Space | Comment | Error of string | EOF;

datatype token = Token of int * (token_kind * string);

val str_of_kind =
 fn Keyword => "keyword"
  | Ident => "identifier"
  | LongIdent => "long identifier"
  | TypeVar => "type variable"
  | Selector => "record selector"
  | Word => "word"
  | Int => "integer"
  | Real => "real"
  | Char => "character"
  | String => "string"
  | Space => "white space"
  | Comment => "comment"
  | Error _ => "bad input"
  | EOF => "end-of-file";


(* end-of-file *)

val eof = Token (0, (EOF, ""));

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;


(* token kind *)

fun kind_of (Token (_, (k, _))) = k;

fun is_kind k (Token (_, (k', _))) = k = k';

fun is_proper (Token (_, (Space, _))) = false
  | is_proper (Token (_, (Comment, _))) = false
  | is_proper _ = true;


(* token value *)

fun val_of (Token (_, (_, x))) = x;

fun token_leq (Token (_, (_, x)), Token (_, (_, x'))) = x <= x';



(** scanners **)

(* diagnostics *)

fun lex_err msg ((n, cs), _) = "SML lexical error (line " ^ string_of_int n ^ "): " ^ msg cs;
fun !!! msg scan = Scan.!! (lex_err (K msg)) scan;


(* line numbering *)

fun incr_line scan = Scan.depend (fn n => scan >> pair (n + 1));
val keep_line = Scan.lift;

val scan_blank =
  incr_line ($$ "\n") ||
  keep_line (Scan.one Symbol.is_ascii_blank);

val scan_blanks = Scan.repeat scan_blank >> implode;
val scan_blanks1 = Scan.repeat1 scan_blank >> implode;


(* keywords *)

val keywords = ["#", "(", ")", ",", "->", "...", ":", ":>", ";", "=",
  "=>", "[", "]", "_", "{", "|", "}", "abstype", "and", "andalso", "as",
  "case", "datatype", "do", "else", "end", "eqtype", "exception", "fn",
  "fun", "functor", "handle", "if", "in", "include", "infix", "infixr",
  "let", "local", "nonfix", "of", "op", "open", "orelse", "raise", "rec",
  "sharing", "sig", "signature", "struct", "structure", "then", "type",
  "val", "where", "while", "with", "withtype"];

val scan_keyword = Scan.literal (Scan.make_lexicon (map explode keywords)) >> implode;


(* identifiers *)

val scan_letdigs =
  Scan.many (Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf Symbol.is_ascii_quasi) >> implode;

val scan_alphanumeric = Scan.one Symbol.is_ascii_letter ^^ scan_letdigs;

val scan_symbolic = Scan.many1 (member (op =) (explode "!#$%&*+-/:<=>?@\\^`|~")) >> implode;

val scan_ident = scan_alphanumeric || scan_symbolic;

val scan_longident =
  (Scan.repeat1 (scan_alphanumeric ^^ $$ ".") >> implode) ^^ (scan_ident || $$ "=");

val scan_typevar = $$ "'" ^^ scan_letdigs;


(* selectors -- not fully standard conformant *)

val scan_numeric =
  Scan.one (member (op =) (explode "123456789")) ^^ (Scan.many Symbol.is_ascii_digit >> implode);

val scan_selector =
  keep_line ($$ "#") ^^ scan_blanks ^^
  !!! "malformed record selector" (keep_line (scan_numeric || scan_alphanumeric || scan_symbolic));


(* numerals *)

val scan_dec = Scan.many1 Symbol.is_ascii_digit >> implode;
val scan_hex = Scan.many1 Symbol.is_ascii_hex >> implode;
val scan_sign = Scan.optional ($$ "~") "";
val scan_decint = scan_sign ^^ scan_dec;

val scan_word = Scan.this_string "0wx" ^^ scan_hex || Scan.this_string "0w" ^^ scan_dec;

val scan_int = scan_sign ^^ (Scan.this_string "0x" ^^ scan_hex || scan_dec);

val scan_exp = ($$ "E" || $$ "e") ^^ scan_decint;

val scan_real =
  scan_decint ^^ $$ "." ^^ scan_dec ^^ Scan.optional scan_exp "" ||
  scan_decint ^^ scan_exp;


(* chars and strings *)

val scan_gap = keep_line ($$ "\\") ^^ scan_blanks1 ^^ keep_line ($$ "\\");
val scan_gaps = Scan.repeat scan_gap >> implode;

val scan_str =
  scan_blank ||
  scan_gap ||
  keep_line ($$ "\\") |-- !!! "bad escape character in string"
      (scan_blank || keep_line ($$ "\"" || $$ "\\")) ||
  keep_line (Scan.one (fn s => s <> "\"" andalso s <> "\\" andalso Symbol.is_regular s));

val scan_char =
  keep_line ($$ "#" ^^ $$ "\"") ^^ scan_gaps ^^ scan_str ^^ scan_gaps ^^ keep_line ($$ "\"");

val scan_string =
  keep_line ($$ "\"") ^^
    !!! "missing quote at end of string" ((Scan.repeat scan_str >> implode) ^^ keep_line ($$ "\""));


(* scan nested comments *)

val scan_cmt =
  Scan.lift scan_blank ||
  Scan.depend (fn d => keep_line ($$ "(" ^^ $$ "*") >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => keep_line ($$ "*" ^^ $$ ")") >> pair (d - 1)) ||
  Scan.lift (keep_line ($$ "*" --| Scan.ahead (~$$ ")"))) ||
  Scan.lift (keep_line (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s)));

val scan_comment =
  keep_line ($$ "(" ^^ $$ "*") ^^
    !!! "missing end of comment"
      (Scan.pass 0 (Scan.repeat scan_cmt >> implode) ^^ keep_line ($$ "*" ^^ $$ ")"));


(* scan token *)

val scan =
  let
    val scanner = Scan.state :|-- (fn n =>
      let
        fun token k x = Token (n, (k, x));
      in
        scan_char >> token Char ||
        scan_selector >> token Selector ||
        scan_string >> token String ||
        scan_blanks1 >> token Space ||
        scan_comment >> token Comment ||
        keep_line (Scan.max token_leq
          (scan_keyword >> token Keyword)
          (scan_longident >> token LongIdent ||
            scan_ident >> token Ident ||
            scan_typevar >> token TypeVar ||
            scan_real >> token Real ||
            scan_word >> token Word ||
            scan_int >> token Int))
      end);
  in !! (lex_err (fn cs => "bad input " ^ quote (Symbol.beginning 10 cs))) scanner end;


(* token sources *)

local

val is_junk = (not o Symbol.is_blank) andf Symbol.is_regular;

fun recover msg = Scan.state :|-- (fn n =>
  keep_line (Scan.many is_junk) >> (fn cs => [Token (n, (Error msg, implode cs))]));

in

fun source do_recover src =
  Source.source' 1 Symbol.stopper (Scan.bulk scan) (Option.map (rpair recover) do_recover) src;

end;

fun source_proper src = src |> Source.filter is_proper;


end;
