(*  Title:      Pure/Isar/outer_lex.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Outer lexical syntax for Isabelle/Isar.
*)

signature OUTER_LEX =
sig
  datatype token_kind =
    Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar | Nat |
    String | AltString | Verbatim | Space | Comment | Malformed | Error of string | Sync | EOF
  eqtype token
  val str_of_kind: token_kind -> string
  val range_of: token -> Position.range
  val position_of: token -> Position.T
  val pos_of: token -> string
  val eof: token
  val is_eof: token -> bool
  val not_eof: token -> bool
  val not_sync: token -> bool
  val stopper: token Scan.stopper
  val kind_of: token -> token_kind
  val is_kind: token_kind -> token -> bool
  val keyword_with: (string -> bool) -> token -> bool
  val ident_with: (string -> bool) -> token -> bool
  val is_proper: token -> bool
  val is_semicolon: token -> bool
  val is_comment: token -> bool
  val is_begin_ignore: token -> bool
  val is_end_ignore: token -> bool
  val is_blank: token -> bool
  val is_newline: token -> bool
  val val_of: token -> string
  val clean_value: Symbol.symbol list -> Symbol.symbol list
  val source_of: token -> string
  val unparse: token -> string
  val text_of: token -> string * string
  val is_sid: string -> bool
  val !!! : string -> (Position.T * 'a -> 'b) -> Position.T * 'a -> 'b
  val scan_string: Position.T * Symbol.symbol list ->
    Symbol.symbol list * (Position.T * Symbol.symbol list)
  val scan: (Scan.lexicon * Scan.lexicon) ->
    Position.T * Symbol.symbol list -> token * (Position.T * Symbol.symbol list)
  val source: bool option -> (unit -> Scan.lexicon * Scan.lexicon) ->
    Position.T -> (Symbol.symbol, 'a) Source.source ->
    (token, Position.T * (Symbol.symbol, 'a) Source.source) Source.source
  val source_proper: (token, 'a) Source.source ->
    (token, (token, 'a) Source.source) Source.source
end;

structure OuterLex: OUTER_LEX =
struct


(** tokens **)

(* datatype token *)

datatype token_kind =
  Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar | Nat |
  String | AltString | Verbatim | Space | Comment | Malformed | Error of string | Sync | EOF;

datatype token = Token of (Position.range * string) * (token_kind * string);

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
  | AltString => "back-quoted string"
  | Verbatim => "verbatim text"
  | Space => "white space"
  | Comment => "comment text"
  | Malformed => "malformed symbolic character"
  | Error _ => "bad input"
  | Sync => "sync marker"
  | EOF => "end-of-file";


(* position *)

fun range_of (Token ((range, _), _)) = range;

val position_of = #1 o range_of;
val pos_of = Position.str_of o position_of;


(* control tokens *)

fun mk_eof pos = Token (((pos, Position.none), ""), (EOF, ""));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

fun not_sync (Token (_, (Sync, _))) = false
  | not_sync _ = true;

val stopper = Scan.stopper (fn [] => eof | toks => mk_eof (#2 (range_of (List.last toks)))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _))) = k;

fun is_kind k (Token (_, (k', _))) = k = k';

fun keyword_with pred (Token (_, (Keyword, x))) = pred x
  | keyword_with _ _ = false;

fun ident_with pred (Token (_, (Ident, x))) = pred x
  | ident_with _ _ = false;

fun is_proper (Token (_, (Space, _))) = false
  | is_proper (Token (_, (Comment, _))) = false
  | is_proper _ = true;

fun is_semicolon (Token (_, (Keyword, ";"))) = true
  | is_semicolon _ = false;

fun is_comment (Token (_, (Comment, _))) = true
  | is_comment _ = false;

fun is_begin_ignore (Token (_, (Comment, "<"))) = true
  | is_begin_ignore _ = false;

fun is_end_ignore (Token (_, (Comment, ">"))) = true
  | is_end_ignore _ = false;


(* blanks and newlines -- space tokens obey lines *)

fun is_blank (Token (_, (Space, x))) = not (String.isSuffix "\n" x)
  | is_blank _ = false;

fun is_newline (Token (_, (Space, x))) = String.isSuffix "\n" x
  | is_newline _ = false;


(* token content *)

fun val_of (Token (_, (_, x))) = x;

val clean_value = filter_out (fn s => s = Symbol.DEL);

fun source_of (Token ((range, src), _)) =
  XML.Elem (Markup.tokenN, Position.properties_of (Position.encode_range range), [XML.Text src])
  |> YXML.string_of;


(* unparse *)

fun escape q =
  implode o map (fn s => if s = q orelse s = "\\" then "\\" ^ s else s) o Symbol.explode;

fun unparse (Token (_, (kind, x))) =
  (case kind of
    String => x |> quote o escape "\""
  | AltString => x |> enclose "`" "`" o escape "`"
  | Verbatim => x |> enclose "{*" "*}"
  | Comment => x |> enclose "(*" "*)"
  | Malformed => Output.escape (translate_string Output.output x)
  | Sync => ""
  | EOF => ""
  | _ => x);

fun text_of tok =
  if is_semicolon tok then ("terminator", "")
  else
    let
      val k = str_of_kind (kind_of tok);
      val s = unparse tok
        handle ERROR _ => Symbol.separate_chars (val_of tok);
    in
      if s = "" then (k, "")
      else if size s < 40 andalso not (exists_string (fn c => c = "\n") s) then (k ^ " " ^ s, "")
      else (k, s)
    end;



(** scanners **)

fun change_prompt scan = Scan.prompt "# " scan;


(* diagnostics *)

fun lex_err msg ((pos, cs), _) = "Outer lexical error" ^ Position.str_of pos ^ ": " ^ msg cs;
fun !!! msg scan = Scan.!! (lex_err (K msg)) scan;


(* scan symbolic idents *)

val is_sym_char = member (op =) (explode "!#$%&*+-/<=>?@^_|~");

val scan_symid =
  Scan.many1 is_sym_char ||
  Scan.one Symbol.is_symbolic >> single;

fun is_symid str =
  (case try Symbol.explode str of
    SOME [s] => Symbol.is_symbolic s orelse is_sym_char s
  | SOME ss => forall is_sym_char ss
  | _ => false);

fun is_sid "begin" = false
  | is_sid ":" = true
  | is_sid "::" = true
  | is_sid s = is_symid s orelse Syntax.is_identifier s;


(* scan strings *)

local

val char_code =
  Scan.one Symbol.is_ascii_digit --
  Scan.one Symbol.is_ascii_digit --
  Scan.one Symbol.is_ascii_digit :|--
  (fn ((a, b), c) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed [chr n, Symbol.DEL, Symbol.DEL] else Scan.fail end);

fun scan_str q =
  Scan.lift ($$ "\\") |-- !!! "bad escape character in string"
    (Scan.lift (($$ q || $$ "\\") >> single || char_code) >> cons Symbol.DEL) ||
  Scan.lift (Scan.one (fn s => s <> q andalso s <> "\\" andalso Symbol.is_regular s) >> single);

fun scan_strs q =
  Scan.lift ($$ q) |-- !!! "missing quote at end of string"
    (change_prompt (Scan.repeat (scan_str q) --| Scan.lift ($$ q)))
  >> (fn body => Symbol.DEL :: flat body @ [Symbol.DEL]);

in

val scan_string = scan_strs "\"";
val scan_alt_string = scan_strs "`";

end;


(* scan verbatim text *)

val scan_verb =
  $$ "*" --| Scan.ahead (~$$ "}") ||
  Scan.one (fn s => s <> "*" andalso Symbol.is_regular s);

val scan_verbatim =
  Scan.lift ($$ "{" |-- $$ "*") |-- !!! "missing end of verbatim text"
    (Scan.lift (change_prompt (Scan.repeat scan_verb --| $$ "*" --| $$ "}")))
  >> (fn body => Symbol.DEL :: Symbol.DEL :: body @ [Symbol.DEL, Symbol.DEL]);


(* scan space *)

fun is_space s = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  (Scan.many1 is_space @@@ Scan.optional ($$ "\n" >> single) [] ||
    Scan.many is_space @@@ ($$ "\n" >> single));


(* scan nested comments *)

val scan_cmt =
  Scan.depend (fn d => $$ "(" -- $$ "*" >> (fn (a, b) => (d + 1, [a, b]))) ||
  Scan.depend (fn 0 => Scan.fail | d => $$ "*" -- $$ ")" >> (fn (a, b) => (d - 1, [a, b]))) ||
  Scan.lift ($$ "*" --| Scan.ahead (~$$ ")") >> single) ||
  Scan.lift (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s) >> single);

val scan_comment =
  Scan.lift ($$ "(" |-- $$ "*") |--
    !!! "missing end of comment"
      (Scan.lift (change_prompt (Scan.pass 0 (Scan.repeat scan_cmt) --| $$ "*" --| $$ ")")))
  >> (fn body => Symbol.DEL :: Symbol.DEL :: flat body @ [Symbol.DEL, Symbol.DEL]);


(* scan malformed symbols *)

val scan_malformed =
  $$ Symbol.malformed |--
    change_prompt (Scan.many Symbol.is_regular)
  --| Scan.option ($$ Symbol.end_malformed);


(* scan token *)

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun scan (lex1, lex2) =
  let
    val scanner =
      (scan_string >> pair String ||
        scan_alt_string >> pair AltString ||
        scan_verbatim >> pair Verbatim ||
        scan_comment >> pair Comment ||
        Scan.lift scan_space >> pair Space ||
        Scan.lift scan_malformed >> pair Malformed ||
        Scan.lift (Scan.one Symbol.is_sync >> K (Sync, [Symbol.sync])) ||
        Scan.lift ((Scan.max token_leq
          (Scan.max token_leq
            (Scan.literal lex2 >> pair Command)
            (Scan.literal lex1 >> pair Keyword))
          (Syntax.scan_longid >> pair LongIdent ||
            Syntax.scan_id >> pair Ident ||
            Syntax.scan_var >> pair Var ||
            Syntax.scan_tid >> pair TypeIdent ||
            Syntax.scan_tvar >> pair TypeVar ||
            Syntax.scan_nat >> pair Nat ||
            scan_symid >> pair SymIdent)))) :|--
      (fn (k, syms) => Scan.depend (fn pos =>
        let
          val pos' = Position.advance syms pos;
          val x = implode (clean_value syms);
        in Scan.succeed (pos', Token (((pos, pos'), implode syms), (k, x))) end));

  in !! (lex_err (fn cs => "bad input " ^ quote (Symbol.beginning 10 cs))) scanner end;


(* token sources *)

local

val is_junk = (not o Symbol.is_blank) andf Symbol.is_regular;

fun recover msg = Scan.lift (Scan.many is_junk) :|-- (fn syms => Scan.depend (fn pos =>
  let
    val pos' = Position.advance syms pos;
    val x = implode (clean_value syms);
  in Scan.succeed (pos', [Token (((pos, pos'), implode syms), (Error msg, x))]) end));

in

fun source do_recover get_lex pos src =
  Source.source' pos Symbol.stopper (Scan.bulk (fn xs => scan (get_lex ()) xs))
    (Option.map (rpair recover) do_recover) src;

end;

fun source_proper src = src |> Source.filter is_proper;

end;
