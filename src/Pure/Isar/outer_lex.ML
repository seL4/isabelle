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
  val position_of: token -> Position.T
  val end_position_of: token -> Position.T
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
  val source_of: token -> string
  val unparse: token -> string
  val text_of: token -> string * string
  val is_sid: string -> bool
  val !!! : string -> (SymbolPos.T list -> 'a) -> SymbolPos.T list -> 'a
  val scan_quoted: SymbolPos.T list -> SymbolPos.T list * SymbolPos.T list
  val source_proper: (token, 'a) Source.source -> (token, (token, 'a) Source.source) Source.source
  val source': bool Option.option -> (unit -> Scan.lexicon * Scan.lexicon) ->
    (SymbolPos.T, 'a) Source.source -> (token, (SymbolPos.T, 'a) Source.source) Source.source
  val source: bool Option.option -> (unit -> Scan.lexicon * Scan.lexicon) ->
    Position.T -> (Symbol.symbol, 'a) Source.source -> (token,
      (SymbolPos.T, Position.T * (Symbol.symbol, 'a) Source.source) Source.source) Source.source
end;

structure OuterLex: OUTER_LEX =
struct

(** tokens **)

(* datatype token *)

datatype token_kind =
  Command | Keyword | Ident | LongIdent | SymIdent | Var | TypeIdent | TypeVar | Nat |
  String | AltString | Verbatim | Space | Comment | Malformed | Error of string | Sync | EOF;

datatype token = Token of (SymbolPos.text * Position.range) * (token_kind * string);

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

fun position_of (Token ((_, (pos, _)), _)) = pos;
fun end_position_of (Token ((_, (_, pos)), _)) = pos;

val pos_of = Position.str_of o position_of;


(* control tokens *)

fun mk_eof pos = Token (("", (pos, Position.none)), (EOF, ""));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

fun not_sync (Token (_, (Sync, _))) = false
  | not_sync _ = true;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_position_of (List.last toks))) is_eof;


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

fun source_of (Token ((source, (pos, _)), _)) =
  YXML.string_of (XML.Elem (Markup.tokenN, Position.properties_of pos, [XML.Text source]));


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

open BasicSymbolPos;

fun !!! msg = SymbolPos.!!! ("Outer lexical error: " ^ msg);

fun change_prompt scan = Scan.prompt "# " scan;


(* scan symbolic idents *)

val is_sym_char = member (op =) (explode "!#$%&*+-/<=>?@^_|~");

val scan_symid =
  Scan.many1 (is_sym_char o symbol) ||
  Scan.one (Symbol.is_symbolic o symbol) >> single;

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
  Scan.one (Symbol.is_ascii_digit o symbol) --
  Scan.one (Symbol.is_ascii_digit o symbol) --
  Scan.one (Symbol.is_ascii_digit o symbol) :|--
  (fn (((a, pos), (b, _)), (c, _)) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed [(chr n, pos)] else Scan.fail end);

fun scan_str q =
  $$$ "\\" |-- !!! "bad escape character in string" ($$$ q || $$$ "\\" || char_code) ||
  Scan.one (fn (s, _) => s <> q andalso s <> "\\" andalso Symbol.is_regular s) >> single;

fun scan_strs q =
  (SymbolPos.scan_pos --| $$$ q) -- !!! "missing quote at end of string"
    (change_prompt ((Scan.repeat (scan_str q) >> flat) -- ($$$ q |-- SymbolPos.scan_pos)));

in

val scan_string = scan_strs "\"";
val scan_alt_string = scan_strs "`";

val scan_quoted = Scan.trace (scan_string || scan_alt_string) >> #2;

end;


(* scan verbatim text *)

val scan_verb =
  $$$ "*" --| Scan.ahead (~$$$ "}") ||
  Scan.one (fn (s, _) => s <> "*" andalso Symbol.is_regular s) >> single;

val scan_verbatim =
  (SymbolPos.scan_pos --| $$$ "{" --| $$$ "*") -- !!! "missing end of verbatim text"
    (change_prompt ((Scan.repeat scan_verb >> flat) -- ($$$ "*" |-- $$$ "}" |-- SymbolPos.scan_pos)));


(* scan space *)

fun is_space s = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  Scan.many1 (is_space o symbol) @@@ Scan.optional ($$$ "\n") [] ||
  Scan.many (is_space o symbol) @@@ $$$ "\n";


(* scan comment *)

val scan_comment =
  SymbolPos.scan_pos -- (SymbolPos.scan_comment_body !!! -- SymbolPos.scan_pos);


(* scan malformed symbols *)

val scan_malformed =
  $$$ Symbol.malformed |--
    change_prompt (Scan.many (Symbol.is_regular o symbol))
  --| Scan.option ($$$ Symbol.end_malformed);



(** token sources **)

fun source_proper src = src |> Source.filter is_proper;

local

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun token k ss =
  Token ((SymbolPos.implode ss, SymbolPos.range ss), (k, SymbolPos.content ss));

fun token_range k (pos1, (ss, pos2)) =
  Token (SymbolPos.implode_range pos1 pos2 ss, (k, SymbolPos.content ss));

fun scan (lex1, lex2) = !!! "bad input"
  (scan_string >> token_range String ||
    scan_alt_string >> token_range AltString ||
    scan_verbatim >> token_range Verbatim ||
    scan_comment >> token_range Comment ||
    scan_space >> token Space ||
    scan_malformed >> token Malformed ||
    Scan.one (Symbol.is_sync o symbol) >> (token Sync o single) ||
    (Scan.max token_leq
      (Scan.max token_leq
        (Scan.literal lex2 >> pair Command)
        (Scan.literal lex1 >> pair Keyword))
      (Syntax.scan_longid >> pair LongIdent ||
        Syntax.scan_id >> pair Ident ||
        Syntax.scan_var >> pair Var ||
        Syntax.scan_tid >> pair TypeIdent ||
        Syntax.scan_tvar >> pair TypeVar ||
        Syntax.scan_nat >> pair Nat ||
        scan_symid >> pair SymIdent) >> uncurry token));

fun recover msg =
  Scan.many ((Symbol.is_regular andf (not o Symbol.is_blank)) o symbol)
  >> (single o token (Error msg));

in

fun source' do_recover get_lex =
  Source.source SymbolPos.stopper (Scan.bulk (fn xs => scan (get_lex ()) xs))
    (Option.map (rpair recover) do_recover);

fun source do_recover get_lex pos src =
  SymbolPos.source pos src
  |> source' do_recover get_lex;

end;

end;
