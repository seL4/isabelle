(*  Title:      Pure/Isar/outer_lex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Outer lexical syntax for Isabelle/Isar.
*)

signature OUTER_LEX =
sig
  datatype token_kind =
    Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar |
    Nat | String | Verbatim | Space | Comment | Sync | EOF
  type token
  val str_of_kind: token_kind -> string
  val stopper: token * (token -> bool)
  val not_sync: token -> bool
  val not_eof: token -> bool
  val position_of: token -> Position.T
  val pos_of: token -> string
  val is_kind: token_kind -> token -> bool
  val keyword_with: (string -> bool) -> token -> bool
  val name_of: token -> string
  val is_proper: token -> bool
  val is_semicolon: token -> bool
  val is_begin_ignore: token -> bool
  val is_end_ignore: token -> bool
  val is_newline: token -> bool
  val is_indent: token -> bool
  val val_of: token -> string
  val is_sid: string -> bool
  val !!! : string -> (Position.T * 'a -> 'b) -> Position.T * 'a -> 'b
  val incr_line: ('a -> 'b * 'c) -> Position.T * 'a -> 'b * (Position.T * 'c)
  val keep_line: ('a -> 'b * 'c) -> Position.T * 'a -> 'b * (Position.T * 'c)
  val scan_blank: Position.T * Symbol.symbol list
    -> Symbol.symbol * (Position.T * Symbol.symbol list)
  val scan_string: Position.T * Symbol.symbol list -> string * (Position.T * Symbol.symbol list)
  val scan: (Scan.lexicon * Scan.lexicon) ->
    Position.T * Symbol.symbol list -> token * (Position.T * Symbol.symbol list)
  val source: bool -> (unit -> (Scan.lexicon * Scan.lexicon)) ->
    Position.T -> (Symbol.symbol, 'a) Source.source ->
    (token, Position.T * (Symbol.symbol, 'a) Source.source) Source.source
  val source_proper: (token, 'a) Source.source -> (token, (token, 'a) Source.source) Source.source
  val make_lexicon: string list -> Scan.lexicon
end;

structure OuterLex: OUTER_LEX =
struct


(** tokens **)

(* datatype token *)

datatype token_kind =
  Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar |
  Nat | String | Verbatim | Space | Comment | Sync | EOF;

datatype token = Token of Position.T * (token_kind * string);

val str_of_kind =
 fn Command => "command"
  | Keyword => "keyword"
  | Ident => "identifier"
  | LongIdent => "long identifier"
  | SymIdent => "symbolic identifier"
  | Var => "schematic variable"
  | TypeIdent => "type variable"
  | TypeVar => "schematic type variable"
  | Nat => "number"
  | String => "string"
  | Verbatim => "verbatim text"
  | Space => "white space"
  | Comment => "comment text"
  | Sync => "sync marker"
  | EOF => "end-of-file";


(* sync token *)

fun not_sync (Token (_, (Sync, _))) = false
  | not_sync _ = true;


(* eof token *)

val eof = Token (Position.none, (EOF, ""));

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;


(* get position *)

fun position_of (Token (pos, _)) = pos;
val pos_of = Position.str_of o position_of;


(* kind of token *)

fun is_kind k (Token (_, (k', _))) = k = k';

fun keyword_with pred (Token (_, (Keyword, x))) = pred x
  | keyword_with _ _ = false;

fun is_proper (Token (_, (Space, _))) = false
  | is_proper (Token (_, (Comment, _))) = false
  | is_proper _ = true;

fun is_semicolon (Token (_, (Command, ";"))) = true
  | is_semicolon _ = false;

fun is_begin_ignore (Token (_, (Comment, "<"))) = true
  | is_begin_ignore _ = false;

fun is_end_ignore (Token (_, (Comment, ">"))) = true
  | is_end_ignore _ = false;


(* newline and indentations (note that space tokens obey lines) *)

fun is_newline (Token (_, (Space, "\n"))) = true
  | is_newline _ = false;

fun is_indent (Token (_, (Space, s))) =
      let val n = size s in n > 0 andalso String.substring (s, n - 1, 1) <> "\n" end
  | is_indent _ = false;


(* name and value of token *)

fun name_of (tok as Token (_, (k, x))) =
  if is_semicolon tok then "terminator" else str_of_kind k ^ " " ^ quote x;

fun val_of (Token (_, (_, x))) = x;

fun token_leq (Token (_, (_, x)), Token (_, (_, x'))) = x <= x';



(** scanners **)

fun change_prompt scan = Scan.prompt "# " scan;


(* diagnostics *)

fun lex_err msg ((pos, cs), _) = "Outer lexical error" ^ Position.str_of pos ^ ": " ^ msg cs;
fun !!! msg scan = Scan.!! (lex_err (K msg)) scan;


(* line numbering *)

fun incr_line scan = Scan.depend (fn pos => scan >> pair (Position.inc pos));
val keep_line = Scan.lift;

val scan_blank =
  incr_line ($$ "\n") ||
  keep_line (Scan.one Symbol.is_blank);


(* scan symbolic idents *)

val sym_chars = explode "!#$%&*+-/:<=>?@^_`|~";
fun is_sym_char s = s mem sym_chars;

val scan_symid =
  Scan.any1 is_sym_char >> implode ||
  Scan.one Symbol.is_symbolic;

fun is_symid str =
  (case try Symbol.explode str of
    Some [s] => Symbol.is_symbolic s orelse is_sym_char s
  | Some ss => forall is_sym_char ss
  | _ => false);

val is_sid = is_symid orf Syntax.is_identifier;


(* scan strings *)

val scan_str =
  scan_blank ||
  keep_line ($$ "\\") |-- !!! "bad escape character in string"
      (scan_blank || keep_line ($$ "\"" || $$ "\\")) ||
  keep_line (Scan.one (not_equal "\\" andf not_equal "\"" andf
    Symbol.not_sync andf Symbol.not_eof));

val scan_string =
  keep_line ($$ "\"") |--
    !!! "missing quote at end of string"
      (change_prompt ((Scan.repeat scan_str >> implode) --| keep_line ($$ "\"")));


(* scan verbatim text *)

val scan_verb =
  scan_blank ||
  keep_line ($$ "*" --| Scan.ahead (Scan.one (not_equal "}"))) ||
  keep_line (Scan.one (not_equal "*" andf Symbol.not_sync andf Symbol.not_eof));

val scan_verbatim =
  keep_line ($$ "{" -- $$ "*") |--
    !!! "missing end of verbatim text"
      (change_prompt ((Scan.repeat scan_verb >> implode) --| keep_line ($$ "*" -- $$ "}")));


(* scan space *)

val is_space = Symbol.is_blank andf not_equal "\n";

val scan_space =
  (keep_line (Scan.any1 is_space) -- Scan.optional (incr_line ($$ "\n")) "" ||
    keep_line (Scan.any is_space) -- incr_line ($$ "\n")) >> (fn (cs, c) => implode cs ^ c);


(* scan nested comments *)

val scan_cmt =
  Scan.lift scan_blank ||
  Scan.depend (fn d => keep_line ($$ "(" ^^ $$ "*") >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => keep_line ($$ "*" ^^ $$ ")") >> pair (d - 1)) ||
  Scan.lift (keep_line ($$ "*" --| Scan.ahead (Scan.one (not_equal ")")))) ||
  Scan.lift (keep_line (Scan.one (not_equal "*" andf Symbol.not_sync andf Symbol.not_eof)));

val scan_comment =
  keep_line ($$ "(" -- $$ "*") |--
    !!! "missing end of comment"
      (change_prompt
        (Scan.pass 0 (Scan.repeat scan_cmt >> implode) --| keep_line ($$ "*" -- $$ ")")));


(* scan token *)

fun scan (lex1, lex2) =
  let
    val scanner = Scan.state :-- (fn pos =>
      let
        fun token k x = Token (pos, (k, x));
        fun sync _ = token Sync Symbol.sync;
      in
        scan_string >> token String ||
        scan_verbatim >> token Verbatim ||
        scan_space >> token Space ||
        scan_comment >> token Comment ||
        keep_line (Scan.one Symbol.is_sync >> sync) ||
        keep_line (Scan.max token_leq
          (Scan.max token_leq
            (Scan.literal lex1 >> (token Keyword o implode))
            (Scan.literal lex2 >> (token Command o implode)))
          (Syntax.scan_longid >> token LongIdent ||
            Syntax.scan_id >> token Ident ||
            Syntax.scan_var >> token Var ||
            Syntax.scan_tid >> token TypeIdent ||
            Syntax.scan_tvar >> token TypeVar ||
            Syntax.scan_nat >> token Nat ||
            scan_symid >> token SymIdent))
      end) >> #2;
  in !! (lex_err (fn cs => "bad input " ^ quote (Symbol.beginning cs))) scanner end;


(* token sources *)

val is_junk = (not o Symbol.is_blank) andf Symbol.not_sync andf Symbol.not_eof;
fun recover xs = keep_line (Scan.any is_junk) xs;

fun source do_recover get_lex pos src =
  Source.source' pos Symbol.stopper (Scan.bulk (fn xs => scan (get_lex ()) xs))
    (if do_recover then Some recover else None) src;

fun source_proper src = src |> Source.filter is_proper;


(* lexicons *)

val make_lexicon = Scan.make_lexicon o map Symbol.explode;

end;
