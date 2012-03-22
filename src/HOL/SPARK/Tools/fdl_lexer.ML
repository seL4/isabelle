(*  Title:      HOL/SPARK/Tools/fdl_lexer.ML
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Lexical analyzer for fdl files.
*)

signature FDL_LEXER =
sig
  type T
  type chars
  type banner
  type date
  type time
  datatype kind = Keyword | Ident | Long_Ident | Traceability | Number | Comment | EOF
  val tokenize: (chars -> 'a * chars) -> (chars -> T * chars) ->
    Position.T -> string -> 'a * T list
  val position_of: T -> Position.T
  val pos_of: T -> string
  val is_eof: T -> bool
  val stopper: T Scan.stopper
  val kind_of: T -> kind
  val content_of: T -> string
  val unparse: T -> string
  val is_proper: T -> bool
  val is_digit: string -> bool
  val c_comment: chars -> T * chars
  val curly_comment: chars -> T * chars
  val percent_comment: chars -> T * chars
  val vcg_header: chars -> (banner * (date * time) option) * chars
  val siv_header: chars ->
    (banner * (date * time) * (date * time) * (string * string)) * chars
end;

structure Fdl_Lexer: FDL_LEXER =
struct

(** tokens **)

datatype kind = Keyword | Ident | Long_Ident | Traceability | Number | Comment | EOF;

datatype T = Token of kind * string * Position.T;

fun make_token k xs = Token (k, implode (map fst xs),
  case xs of [] => Position.none | (_, p) :: _ => p);

fun kind_of (Token (k, _, _)) = k;

fun is_proper (Token (Comment, _, _)) = false
  | is_proper _ = true;

fun content_of (Token (_, s, _)) = s;

fun unparse (Token (Traceability, s, _)) = "For " ^ s ^ ":"
  | unparse (Token (_, s, _)) = s;

fun position_of (Token (_, _, pos)) = pos;

val pos_of = Position.str_of o position_of;

fun is_eof (Token (EOF, _, _)) = true
  | is_eof _ = false;

fun mk_eof pos = Token (EOF, "", pos);
val eof = mk_eof Position.none;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (position_of (List.last toks))) is_eof;

fun leq_token (Token (_, s, _), Token (_, s', _)) = size s <= size s';


(** split up a string into a list of characters (with positions) **)

type chars = (string * Position.T) list;

fun is_char_eof ("", _) = true
  | is_char_eof _ = false;

val char_stopper = Scan.stopper (K ("", Position.none)) is_char_eof;

fun symbol (x : string, _ : Position.T) = x;

fun explode_pos s pos = fst (fold_map (fn x => fn pos =>
  ((x, pos), Position.advance x pos)) (raw_explode s) pos);


(** scanners **)

val any = Scan.one (not o Scan.is_stopper char_stopper);

fun prfx [] = Scan.succeed []
  | prfx (x :: xs) = Scan.one (equal x o symbol) ::: prfx xs;

val $$$ = prfx o raw_explode;

val lexicon = Scan.make_lexicon (map raw_explode
  ["rule_family",
   "For",
   ":",
   "[",
   "]",
   "(",
   ")",
   ",",
   "&",
   ";",
   "=",
   ".",
   "..",
   "requires",
   "may_be_replaced_by",
   "may_be_deduced",
   "may_be_deduced_from",
   "are_interchangeable",
   "if",
   "end",
   "function",
   "procedure",
   "type",
   "var",
   "const",
   "array",
   "record",
   ":=",
   "of",
   "**",
   "*",
   "/",
   "div",
   "mod",
   "+",
   "-",
   "<>",
   "<",
   ">",
   "<=",
   ">=",
   "<->",
   "->",
   "not",
   "and",
   "or",
   "for_some",
   "for_all",
   "***",
   "!!!",
   "element",
   "update",
   "pending"]);

fun keyword s = Scan.literal lexicon :|--
  (fn xs => if map symbol xs = raw_explode s then Scan.succeed xs else Scan.fail);

fun is_digit x = "0" <= x andalso x <= "9";
fun is_alpha x = "a" <= x andalso x <= "z" orelse "A" <= x andalso x <= "Z";
val is_underscore = equal "_";
val is_tilde = equal "~";
val is_newline = equal "\n";
val is_tab = equal "\t";
val is_space = equal " ";
val is_whitespace = is_space orf is_tab orf is_newline;
val is_whitespace' = is_space orf is_tab;

val number = Scan.many1 (is_digit o symbol);

val identifier =
  Scan.one (is_alpha o symbol) :::
  Scan.many
    ((is_alpha orf is_digit orf is_underscore) o symbol) @@@
   Scan.optional (Scan.one (is_tilde o symbol) >> single) [];

val long_identifier =
  identifier @@@ (Scan.repeat1 ($$$ "." @@@ identifier) >> flat);

val whitespace = Scan.many (is_whitespace o symbol);
val whitespace' = Scan.many (is_whitespace' o symbol);
val newline = Scan.one (is_newline o symbol);

fun beginning n cs =
  let
    val drop_blanks = #1 o take_suffix is_whitespace;
    val all_cs = drop_blanks cs;
    val dots = if length all_cs > n then " ..." else "";
  in
    (drop_blanks (take n all_cs)
      |> map (fn c => if is_whitespace c then " " else c)
      |> implode) ^ dots
  end;

fun !!! text scan =
  let
    fun get_pos [] = " (past end-of-text!)"
      | get_pos ((_, pos) :: _) = Position.str_of pos;

    fun err (syms, msg) = fn () =>
      text ^ get_pos syms ^ " at " ^ beginning 10 (map symbol syms) ^
        (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end;

val any_line' =
  Scan.many (not o (Scan.is_stopper char_stopper orf (is_newline o symbol)));

val any_line = whitespace' |-- any_line' --|
  newline >> (implode o map symbol);

fun gen_comment a b = $$$ a |-- !!! "missing end of comment"
  (Scan.repeat (Scan.unless ($$$ b) any) --| $$$ b) >> make_token Comment;

val c_comment = gen_comment "/*" "*/";
val curly_comment = gen_comment "{" "}";

val percent_comment = $$$ "%" |-- any_line' >> make_token Comment;

fun repeatn 0 _ = Scan.succeed []
  | repeatn n p = Scan.one p ::: repeatn (n-1) p;


(** header of *.vcg and *.siv files (see simplifier/load_provenance.pro) **)

type banner = string * string * string;
type date = string * string * string;
type time = string * string * string * string option;

val asterisks = Scan.repeat1 (Scan.one (equal "*" o symbol));

fun alphan n = repeatn n (is_alpha o symbol) >> (implode o map symbol);
fun digitn n = repeatn n (is_digit o symbol) >> (implode o map symbol);

val time =
  digitn 2 --| $$$ ":" -- digitn 2 --| $$$ ":" -- digitn 2 --
  Scan.option ($$$ "." |-- digitn 2) >>
    (fn (((hr, mi), s), ms) => (hr, mi, s, ms));

val date =
  digitn 2 --| $$$ "-" -- alphan 3 --| $$$ "-" -- digitn 4 >>
    (fn ((d, m), y) => (d, m, y));

val banner = 
  whitespace' |-- asterisks --| whitespace' --| newline :|-- (fn xs =>
    (any_line -- any_line -- any_line >>
       (fn ((l1, l2), l3) => (l1, l2, l3))) --|
    whitespace' --| prfx (map symbol xs) --| whitespace' --| newline);

val vcg_header = banner -- Scan.option (whitespace |--
  $$$ "DATE :" |-- whitespace |-- date --| whitespace --|
  Scan.option ($$$ "TIME :" -- whitespace) -- time);

val siv_header = banner --| whitespace --
  ($$$ "CREATED" |-- whitespace |-- (date --| $$$ "," --| whitespace -- time)) --|
  whitespace --
  ($$$ "SIMPLIFIED" |-- whitespace |-- (date --| $$$ "," --| whitespace -- time)) --|
  newline --| newline -- (any_line -- any_line) >>
    (fn (((b, c), s), ls) => (b, c, s, ls));


(** the main tokenizer **)

fun scan header comment =
  !!! "bad header" header --| whitespace --
  Scan.repeat (Scan.unless (Scan.one is_char_eof)
    (!!! "bad input"
       (   comment
        || (keyword "For" -- whitespace) |--
              Scan.repeat1 (Scan.unless (keyword ":") any) --|
              keyword ":" >> make_token Traceability
        || Scan.max leq_token
             (Scan.literal lexicon >> make_token Keyword)
             (   long_identifier >> make_token Long_Ident
              || identifier >> make_token Ident)
        || number >> make_token Number) --|
     whitespace));

fun tokenize header comment pos s =
  fst (Scan.finite char_stopper
    (Scan.error (scan header comment)) (explode_pos s pos));

end;
