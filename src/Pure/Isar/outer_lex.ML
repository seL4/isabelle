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
  val stopper: token * (token -> bool)
  val not_sync: token -> bool
  val not_eof: token -> bool
  val position_of: token -> Position.T
  val pos_of: token -> string
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
  val unparse: token -> string
  val text_of: token -> string * string
  val is_sid: string -> bool
  val !!! : string -> (Position.T * 'a -> 'b) -> Position.T * 'a -> 'b
  val count: (Symbol.symbol list -> Symbol.symbol * Symbol.symbol list) ->
    Position.T * Symbol.symbol list -> Symbol.symbol * (Position.T * Symbol.symbol list)
  val counted: (Symbol.symbol list -> Symbol.symbol list * Symbol.symbol list) ->
    Position.T * Symbol.symbol list -> string * (Position.T * Symbol.symbol list)
  val scan_string: Position.T * Symbol.symbol list -> string * (Position.T * Symbol.symbol list)
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
  | AltString => "back-quoted string"
  | Verbatim => "verbatim text"
  | Space => "white space"
  | Comment => "comment text"
  | Malformed => "malformed symbolic character"
  | Error _ => "bad input"
  | Sync => "sync marker"
  | EOF => "end-of-file";


(* control tokens *)

val eof = Token (Position.none, (EOF, ""));

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper = (eof, is_eof);
val not_eof = not o is_eof;


fun not_sync (Token (_, (Sync, _))) = false
  | not_sync _ = true;


(* get position *)

fun position_of (Token (pos, _)) = pos;
val pos_of = Position.str_of o position_of;


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
fun token_leq (tok1, tok2) = val_of tok1 <= val_of tok2;

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


(* position *)

local

fun map_position f (scan: Symbol.symbol list -> 'a * Symbol.symbol list)  =
  Scan.depend (fn (pos: Position.T) => scan >> (fn x => (f x pos, x)));

in

fun count scan = map_position Position.advance scan;
fun counted scan = map_position (fold Position.advance) scan >> implode;

end;


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
  count (Scan.one Symbol.is_ascii_digit) --
  count (Scan.one Symbol.is_ascii_digit) --
  count (Scan.one Symbol.is_ascii_digit) :|--
  (fn ((a, b), c) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed (chr n) else Scan.fail end);

fun scan_str q =
  count ($$ "\\") |-- !!! "bad escape character in string" (count ($$ q || $$ "\\") || char_code) ||
  count (Scan.one (fn s => s <> q andalso s <> "\\" andalso Symbol.is_regular s));

fun scan_strs q =
  count ($$ q) |--
    !!! "missing quote at end of string"
      (change_prompt ((Scan.repeat (scan_str q) >> implode) --| count ($$ q)));

in

val scan_string = scan_strs "\"";
val scan_alt_string = scan_strs "`";

end;


(* scan verbatim text *)

val scan_verb =
  count ($$ "*" --| Scan.ahead (~$$ "}")) ||
  count (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s));

val scan_verbatim =
  count ($$ "{") |-- count ($$ "*") |--
    !!! "missing end of verbatim text"
      (change_prompt ((Scan.repeat scan_verb >> implode) --| count ($$ "*") --| count ($$ "}")));


(* scan space *)

fun is_space s = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  (Scan.many1 is_space @@@ Scan.optional ($$ "\n" >> single) [] ||
    Scan.many is_space @@@ ($$ "\n" >> single));


(* scan nested comments *)

val scan_cmt =
  Scan.depend (fn d => count ($$ "(") ^^ count ($$ "*") >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => count ($$ "*") ^^ count ($$ ")") >> pair (d - 1)) ||
  Scan.lift (count ($$ "*" --| Scan.ahead (~$$ ")"))) ||
  Scan.lift (count (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s)));

val scan_comment =
  count ($$ "(") |-- count ($$ "*") |--
    !!! "missing end of comment"
      (change_prompt
        (Scan.pass 0 (Scan.repeat scan_cmt >> implode) --| count ($$ "*") --| count ($$ ")")));


(* scan malformed symbols *)

val scan_malformed =
  $$ Symbol.malformed |--
    change_prompt (Scan.many Symbol.is_regular)
  --| Scan.option ($$ Symbol.end_malformed);


(* scan token *)

fun scan (lex1, lex2) =
  let
    val scanner = Scan.state :|-- (fn pos =>
      let
        fun token k x = Token (pos, (k, x));
        fun sync _ = token Sync Symbol.sync;
      in
        scan_string >> token String ||
        scan_alt_string >> token AltString ||
        scan_verbatim >> token Verbatim ||
        scan_comment >> token Comment ||
        counted scan_space >> token Space ||
        counted scan_malformed >> token Malformed ||
        Scan.lift (Scan.one Symbol.is_sync >> sync) ||
        (Scan.max token_leq
          (Scan.max token_leq
            (counted (Scan.literal lex1) >> token Keyword)
            (counted (Scan.literal lex2) >> token Command))
          (counted Syntax.scan_longid >> token LongIdent ||
            counted Syntax.scan_id >> token Ident ||
            counted Syntax.scan_var >> token Var ||
            counted Syntax.scan_tid >> token TypeIdent ||
            counted Syntax.scan_tvar >> token TypeVar ||
            counted Syntax.scan_nat >> token Nat ||
            counted scan_symid >> token SymIdent))
      end);
  in !! (lex_err (fn cs => "bad input " ^ quote (Symbol.beginning 10 cs))) scanner end;


(* token sources *)

local

val is_junk = (not o Symbol.is_blank) andf Symbol.is_regular;

fun recover msg = Scan.state :|-- (fn pos =>
  counted (Scan.many is_junk) >> (fn s => [Token (pos, (Error msg, s))]));

in

fun source do_recover get_lex pos src =
  Source.source' pos Symbol.stopper (Scan.bulk (fn xs => scan (get_lex ()) xs))
    (Option.map (rpair recover) do_recover) src;

end;

fun source_proper src = src |> Source.filter is_proper;


end;
