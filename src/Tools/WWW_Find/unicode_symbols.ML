(*  Title:      Tools/WWW_Find/unicode_symbols.ML
    Author:     Timothy Bourke, NICTA

Parse the ISABELLE_HOME/etc/symbols file.
*)

signature UNICODE_SYMBOLS =
sig
val symbol_to_unicode : string -> int option
val abbrev_to_unicode : string -> int option
val unicode_to_symbol : int -> string option
val unicode_to_abbrev : int -> string option
val utf8_to_symbols   : string -> string
val utf8              : int list -> string
end;

structure UnicodeSymbols : UNICODE_SYMBOLS =
struct

local (* Lexer *)

open Basic_Symbol_Pos

val keywords =
  Scan.make_lexicon (map Symbol.explode ["code", "font", "abbrev", ":"]);

datatype token_kind =
  Symbol | AsciiSymbol | Keyword | Name | Code | Space | Comment | EOF;

datatype token = Token of token_kind * string * Position.range;

fun token kind ss = Token (kind, Symbol_Pos.content ss, Symbol_Pos.range ss);

in

fun mk_eof pos = Token (EOF, "", (pos, Position.none));

fun str_of_token (Token (_, s, _)) = s;

fun pos_of_token (Token (_, _, (pos, _))) = pos;

fun int_of_code (Token (Code, s, _)) = #value (Lexicon.read_xnum s)
  | int_of_code _ = error "internal error in UnicodeSymbols.int_of_code"

fun is_proper (Token (Space, _, _)) = false
  | is_proper (Token (Comment, _, _)) = false
  | is_proper _ = true;

fun is_keyword kw (Token (Keyword, kw', _)) = (kw = kw')
  | is_keyword _ _ = false;

fun is_ascii_sym (Token (AsciiSymbol, _, _)) = true
  | is_ascii_sym _ = false;

fun is_hex_code (Token (Code, _, _)) = true
  | is_hex_code _ = false;

fun is_symbol (Token (Symbol, _, _)) = true
  | is_symbol _ = false;

fun is_name (Token (Name, _, _)) = true
  | is_name _ = false;

fun is_eof (Token (EOF, _, _)) = true
  | is_eof _ = false;

fun end_position_of (Token (_, _, (_, epos))) = epos;

val is_space = Symbol_Pos.symbol #> (fn s => Symbol.is_blank s andalso s <> "\n");
val scan_space =
  (Scan.many1 is_space @@@ Scan.optional ($$$ "\n") []
   ||
   Scan.many is_space @@@ ($$$ "\n")) >> token Space;

val scan_code = Lexicon.scan_hex #>> token Code;

val scan_ascii_symbol = Scan.one
  ((fn x => Symbol.is_ascii x andalso
      not (Symbol.is_ascii_letter x
           orelse Symbol.is_ascii_digit x
           orelse Symbol.is_ascii_blank x)) o Symbol_Pos.symbol)
  -- Scan.many (not o Symbol.is_ascii_blank o Symbol_Pos.symbol)
  >> (token AsciiSymbol o op ::);

fun not_contains xs c = not (member (op =) (raw_explode xs) (Symbol_Pos.symbol c));
val scan_comment =
  $$$ "#" |-- (Scan.many (not_contains "\n") @@@ ($$$ "\n"))
  >> token Comment;

fun is_sym s =
  (case Symbol.decode s of
    Symbol.Sym _ => true
  | Symbol.Ctrl _ => true
  | _ => false);

fun tokenize syms =
  let
    val scanner =
      Scan.one (is_sym o Symbol_Pos.symbol) >> (token Symbol o single) ||
      scan_comment ||
      scan_space ||
      scan_code ||
      Scan.literal keywords >> token Keyword ||
      scan_ascii_symbol ||
      Lexicon.scan_id >> token Name;
    val scan_token = Symbol_Pos.!!! (fn () => "Lexical error") (Scan.bulk scanner);
  in
    (case Scan.error (Scan.finite Symbol_Pos.stopper scan_token) syms of
      (toks, []) => toks
    | (_, ss) =>
        error ("Lexical error at: " ^ Symbol_Pos.content ss ^
          Position.here (#1 (Symbol_Pos.range ss))))
  end;

val stopper =
  Scan.stopper
    (fn [] => mk_eof Position.none
      | toks => mk_eof (end_position_of (List.last toks))) is_eof;

end;

local (* Parser *)

fun $$$ kw = Scan.one (is_keyword kw) >> str_of_token;
val hex_code = Scan.one is_hex_code >> int_of_code;
val ascii_sym = Scan.one is_ascii_sym >> str_of_token;
val symbol = Scan.one is_symbol >> (fn t => (str_of_token t, pos_of_token t));
val name = Scan.one is_name >> str_of_token;

val unicode = $$$ "code" -- $$$ ":" |-- hex_code;
val font = Scan.option ($$$ "font" -- $$$ ":" |-- name);
val abbr = Scan.option ($$$ "abbrev" -- $$$ ":"
                        |-- (ascii_sym || $$$ ":" || name));

in

val line = (symbol -- unicode --| font -- abbr) >> Parse.triple1;

end;

local (* build tables *)

fun add_entries ((fromsym, fromabbr, tosym, toabbr), ((sym, pos), uni, oabbr)) =
  (case oabbr of
     NONE =>
       (Symtab.update_new (sym, uni) fromsym,
        fromabbr,
        Inttab.update (uni, sym) tosym,
        toabbr)
   | SOME abbr =>
       (Symtab.update_new (sym, uni) fromsym,
        Symtab.update_new (abbr, uni) fromabbr,
        Inttab.update (uni, sym) tosym,
        Inttab.update (uni, abbr) toabbr))
  handle Symtab.DUP sym => error ("Duplicate at" ^ Position.here pos)
       | Inttab.DUP sym => error ("Duplicate code at" ^ Position.here pos);

in

fun read_symbols path =
  let
    val parsed_lines =
      Symbol_Pos.explode (File.read path, Path.position path)
      |> tokenize
      |> filter is_proper
      |> Scan.finite stopper (Scan.repeat line)
      |> fst;
  in
    Library.foldl add_entries
      ((Symtab.empty, Symtab.empty, Inttab.empty, Inttab.empty),
       parsed_lines)
  end;

end;

local
val (fromsym, fromabbr, tosym, toabbr) = read_symbols (Path.explode "~~/etc/symbols");
in
val symbol_to_unicode = Symtab.lookup fromsym;
val abbrev_to_unicode = Symtab.lookup fromabbr;
val unicode_to_symbol = Inttab.lookup tosym;
val unicode_to_abbrev = Inttab.lookup toabbr;
end;

fun utf8_to_symbols utf8str =
  let
    val get_next =
      Substring.getc
      #> Option.map (apfst Byte.charToByte);
    val wstr = String.str o Byte.byteToChar;
    val replacement_char = "\<questiondown>";

    fun word_to_symbol w =
      (case (unicode_to_symbol o Word32.toInt) w of
         NONE => "?"
       | SOME s => s);

    fun andb32 (w1, w2) =
      Word8.andb(w1, w2)
      |> Word8.toLarge
      |> Word32.fromLarge;

    fun read_next (ss, 0, c) = (word_to_symbol c, ss)
      | read_next (ss, n, c) =
          (case get_next ss of
             NONE => (replacement_char, ss)
           | SOME (w, ss') =>
               if Word8.andb (w, 0wxc0) <> 0wx80
               then (replacement_char, ss')
               else
                 let
                   val w' = (Word8.andb (w, 0wx3f));
                   val bw = (Word32.fromLarge o Word8.toLarge) w';
                   val c' = Word32.<< (c, 0wx6);
                 in read_next (ss', n - 1, Word32.orb (c', bw)) end);

    fun do_char (w, ss) =
      if Word8.andb (w, 0wx80) = 0wx00
      then (wstr w, ss)
      else if Word8.andb (w, 0wx60) = 0wx40
      then read_next (ss, 1, andb32 (w, 0wx1f))
      else if Word8.andb (w, 0wxf0) = 0wxe0
      then read_next (ss, 2, andb32 (w, 0wx0f))
      else if Word8.andb (w, 0wxf8) = 0wxf0
      then read_next (ss, 3, andb32 (w, 0wx07))
      else (replacement_char, ss);

    fun read (rs, ss) =
      (case Option.map do_char (get_next ss) of
         NONE => (implode o rev) rs
       | SOME (s, ss') => read (s::rs, ss'));
  in read ([], Substring.full utf8str) end;

local

fun consec n =
  fn w => (
    Word32.>> (w, Word.fromInt (n * 6))
    |> (curry Word32.andb) 0wx3f
    |> (curry Word32.orb) 0wx80
    |> Word8.fromLargeWord o Word32.toLargeWord);

fun stamp n =
  fn w => (
    Word32.>> (w, Word.fromInt (n * 6))
    |> (curry Word32.andb) (Word32.>> (0wx000000ff, Word.fromInt (n + 2)))
    |> (curry Word32.orb) (Word32.<< (0wxffffffff, Word.fromInt (7 - n)))
    |> Word8.fromLargeWord o Word32.toLargeWord);

fun to_utf8_bytes i =
  if i <= 0x007f
  then [Word8.fromInt i]
  else let
    val w = Word32.fromInt i;
  in
    if i < 0x07ff
    then [stamp 1 w, consec 0 w]
    else if i < 0xffff
    then [stamp 2 w, consec 1 w, consec 0 w]
    else if i < 0x10ffff
    then [stamp 3 w, consec 2 w, consec 1 w, consec 0 w]
    else []
  end;

in

fun utf8 is =
  map to_utf8_bytes is
  |> flat
  |> Word8Vector.fromList
  |> Byte.bytesToString;

end

end;

