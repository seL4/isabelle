(*  Title:      Pure/Thy/thy_scan.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The scanner for theory files.
*)

signature THY_SCAN =
sig
  datatype token_kind =
    Keyword | Ident | LongIdent | TypeVar | Nat | String | Verbatim | EOF
  val name_of_kind: token_kind -> string
  type lexicon
  val make_lexicon: string list -> lexicon
  val tokenize: lexicon -> string -> (token_kind * string * int) list
end;


functor ThyScanFun(Scanner: SCANNER): THY_SCAN =
struct

open Scanner;


(** token kinds **)

datatype token_kind =
  Keyword | Ident | LongIdent | TypeVar | Nat | String | Verbatim | EOF;

fun name_of_kind Keyword = "keyword"
  | name_of_kind Ident = "identifier"
  | name_of_kind LongIdent = "long identifier"
  | name_of_kind TypeVar = "type variable"
  | name_of_kind Nat = "natural number"
  | name_of_kind String = "string"
  | name_of_kind Verbatim = "verbatim text"
  | name_of_kind EOF = "end-of-file";



(** scanners **)

fun lex_err line msg =
  error ("Lexical error on line " ^ string_of_int line ^ ": " ^ msg);


(* misc utilities *)

fun count_lines cs =
  foldl (fn (sum, c) => if c = "\n" then sum + 1 else sum) (0, cs);

fun inc_line n s = n + count_lines (explode s);

fun cons_fst c (cs, x, y) = (c :: cs, x, y);


(* scan strings *)

val scan_ctrl = $$ "^" ^^ scan_one (fn c => ord c >= 64 andalso ord c <= 95);

val scan_dig = scan_one is_digit;

val scan_blanks1 = scan_any1 is_blank >> implode;

val scan_esc =
  $$ "n" || $$ "t" || $$ "\"" || $$ "\\" ||
  scan_ctrl || scan_dig ^^ scan_dig ^^ scan_dig ||
  scan_blanks1 ^^ $$ "\\";


fun string ("\"" :: cs) n = (["\""], cs, n)
  | string ("\\" :: cs) n =
      (case optional scan_esc cs of
        (None, _) => lex_err n "bad escape sequence in string"
      | (Some s, cs') => cons_fst ("\\" ^ s) (string cs' (inc_line n s)))
  | string (c :: cs) n = 
      if c = "\n" then 
        lex_err n "no matching quote found on this line"
      else cons_fst c (string cs n)
  | string [] n = lex_err n "missing quote at end of string";


(* scan verbatim text *)

fun verbatim ("|" :: "}" :: cs) n = ([], cs, n)
  | verbatim (c :: cs) n = cons_fst c (verbatim cs (inc_line n c))
  | verbatim [] n = lex_err n "missing end of verbatim text";


(* scan nested comments *)

fun comment ("*" :: ")" :: cs) n 1 = (cs, n)
  | comment ("*" :: ")" :: cs) n d = comment cs n (d - 1)
  | comment ("(" :: "*" :: cs) n d = comment cs n (d + 1)
  | comment (c :: cs) n d = comment cs (inc_line n c) d
  | comment [] n _ = lex_err n "missing end of comment";



(** tokenize **)

val scan_longid = scan_id ^^ (repeat1 ($$ "." ^^ scan_id) >> implode);

fun scan_word lex =
  max_of
    (scan_literal lex >> pair Keyword)
    (scan_longid >> pair LongIdent ||
      scan_id >> pair Ident ||
      scan_tid >> pair TypeVar ||
      scan_nat >> pair Nat);

fun add_tok toks kind n (cs, cs', n') =
  ((kind, implode cs, n) :: toks, cs', n');

val take_line = implode o fst o take_prefix (not_equal "\n");


fun tokenize lex str =
  let
    fun scan (toks, [], n) = rev ((EOF, "end-of-file", n) :: toks)
      | scan (toks, "\"" :: cs, n) =
          scan (add_tok toks String n (cons_fst "\"" (string cs n)))
      | scan (toks, "{" :: "|" :: cs, n) =
          scan (add_tok toks Verbatim n (verbatim cs n))
      | scan (toks, "(" :: "*" :: cs, n) =
          scan ((fn (cs', n') => (toks, cs', n')) (comment cs n 1))
      | scan (toks, chs as c :: cs, n) =
          if is_blank c then scan (toks, cs, inc_line n c)
          else
            (case scan_word lex chs of
              (None, _) => lex_err n (quote (take_line chs))
            | (Some (Keyword, "ML"), chs') => scan ((Verbatim, implode chs', n)
                :: (Keyword, "ML", n) :: toks, [], n + count_lines chs')
            | (Some (tk, s), chs') => scan ((tk, s, n) :: toks, chs', n));
  in
    scan ([], explode str, 1)
  end;


end;

