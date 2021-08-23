(*  Title:      Pure/General/symbol_pos.ML
    Author:     Makarius

Symbols with explicit position information.
*)

signature SYMBOL_POS =
sig
  type T = Symbol.symbol * Position.T
  type 'a scanner = T list -> 'a * T list
  val symbol: T -> Symbol.symbol
  val content: T list -> string
  val range: T list -> Position.range
  val is_eof: T -> bool
  val stopper: T Scan.stopper
  val !!! : Scan.message -> 'a scanner -> 'a scanner
  val $$ : Symbol.symbol -> T scanner
  val ~$$ : Symbol.symbol -> T scanner
  val $$$ : Symbol.symbol -> T list scanner
  val ~$$$ : Symbol.symbol -> T list scanner
  val scan_pos: Position.T scanner
  val scan_string_q: string -> (Position.T * (T list * Position.T)) scanner
  val scan_string_qq: string -> (Position.T * (T list * Position.T)) scanner
  val scan_string_bq: string -> (Position.T * (T list * Position.T)) scanner
  val recover_string_q: T list scanner
  val recover_string_qq: T list scanner
  val recover_string_bq: T list scanner
  val quote_string_q: string -> string
  val quote_string_qq: string -> string
  val quote_string_bq: string -> string
  val cartouche_content: T list -> T list
  val scan_cartouche: string -> T list scanner
  val scan_cartouche_content: string -> T list scanner
  val recover_cartouche: T list scanner
  val scan_comment: string -> T list scanner
  val scan_comment_body: string -> T list scanner
  val recover_comment: T list scanner
  val source: Position.T -> (Symbol.symbol, 'a) Source.source ->
    (T, Position.T * (Symbol.symbol, 'a) Source.source) Source.source
  type text = string
  val implode: T list -> text
  val implode_range: Position.range -> T list -> text * Position.range
  val explode_deleted: string * Position.T -> Position.T list
  val explode: text * Position.T -> T list
  val explode0: string -> T list
  val scan_ident: T list scanner
  val is_identifier: string -> bool
  val scan_nat: T list scanner
  val scan_float: T list scanner
end;

structure Symbol_Pos: SYMBOL_POS =
struct

(* type T *)

type T = Symbol.symbol * Position.T;
type 'a scanner = T list -> 'a * T list;

fun symbol ((s, _): T) = s;

val content = implode o map symbol;

fun range (syms as (_, pos) :: _) =
      let val pos' = List.last syms |-> Position.symbol
      in Position.range (pos, pos') end
  | range [] = Position.no_range;


(* stopper *)

fun mk_eof pos = (Symbol.eof, pos);
val eof = mk_eof Position.none;

val is_eof = Symbol.is_eof o symbol;

val stopper =
  Scan.stopper (fn [] => eof | inp => mk_eof (List.last inp |-> Position.symbol)) is_eof;


(* basic scanners *)

fun !!! text (scan: 'a scanner) =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos ((_, pos) :: _) = Position.here pos;

    fun err (syms, msg) = fn () =>
      text () ^ get_pos syms ^
      Markup.markup Markup.no_report (" at " ^ Symbol.beginning 10 (map symbol syms)) ^
      (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end;

fun $$ s = Scan.one (fn x => symbol x = s);
fun ~$$ s = Scan.one (fn x => symbol x <> s);

fun $$$ s = Scan.one (fn x => symbol x = s) >> single;
fun ~$$$ s = Scan.one (fn x => symbol x <> s) >> single;

val scan_pos = Scan.ahead (Scan.one (K true)) >> (fn (_, pos): T => pos);


(* scan string literals *)

local

val char_code =
  Scan.one (Symbol.is_ascii_digit o symbol) --
  Scan.one (Symbol.is_ascii_digit o symbol) --
  Scan.one (Symbol.is_ascii_digit o symbol) :|--
  (fn (((a, pos), (b, _)), (c, _)) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed [(chr n, pos)] else Scan.fail end);

fun scan_str q err_prefix =
  $$$ "\\" |-- !!! (fn () => err_prefix ^ "bad escape character in string")
    ($$$ q || $$$ "\\" || char_code) ||
  Scan.one (fn (s, _) => s <> q andalso s <> "\\" andalso Symbol.not_eof s) >> single;

fun scan_strs q err_prefix =
  Scan.ahead ($$ q) |--
    !!! (fn () => err_prefix ^ "unclosed string literal")
      ((scan_pos --| $$$ q) -- (Scan.repeats (scan_str q err_prefix) -- ($$$ q |-- scan_pos)));

fun recover_strs q =
  $$$ q @@@ Scan.repeats (Scan.permissive (scan_str q ""));

in

val scan_string_q = scan_strs "'";
val scan_string_qq = scan_strs "\"";
val scan_string_bq = scan_strs "`";

val recover_string_q = recover_strs "'";
val recover_string_qq = recover_strs "\"";
val recover_string_bq = recover_strs "`";

end;


(* quote string literals *)

local

fun char_code i =
  (if i < 10 then "00" else if i < 100 then "0" else "") ^ string_of_int i;

fun quote_str q s =
  if Symbol.is_ascii_control s then "\\" ^ char_code (ord s)
  else if s = q orelse s = "\\" then "\\" ^ s
  else s;

fun quote_string q = enclose q q o implode o map (quote_str q) o Symbol.explode;

in

val quote_string_q = quote_string "'";
val quote_string_qq = quote_string "\"";
val quote_string_bq = quote_string "`";

end;


(* nested text cartouches *)

fun cartouche_content syms =
  let
    fun err () =
      error ("Malformed text cartouche: "
        ^ quote (content syms) ^ Position.here (#1 (range syms)));
  in
    (case syms of
      ("\<open>", _) :: rest =>
        (case rev rest of
          ("\<close>", _) :: rrest => rev rrest
        | _ => err ())
    | _ => err ())
  end;

val scan_cartouche_depth =
  Scan.repeat1 (Scan.depend (fn (depth: int option) =>
    (case depth of
      SOME d =>
        $$ Symbol.open_ >> pair (SOME (d + 1)) ||
          (if d > 0 then
            Scan.one (fn (s, _) => s <> Symbol.close andalso Symbol.not_eof s) >> pair depth ||
            $$ Symbol.close >> pair (if d = 1 then NONE else SOME (d - 1))
          else Scan.fail)
    | NONE => Scan.fail)));

fun scan_cartouche err_prefix =
  Scan.ahead ($$ Symbol.open_) |--
    !!! (fn () => err_prefix ^ "unclosed text cartouche")
      (Scan.provide is_none (SOME 0) scan_cartouche_depth);

fun scan_cartouche_content err_prefix =
  scan_cartouche err_prefix >> cartouche_content;

val recover_cartouche = Scan.pass (SOME 0) scan_cartouche_depth;


(* ML-style comments *)

local

val scan_cmt =
  Scan.depend (fn (d: int) => $$$ "(" @@@ $$$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$$ "*" @@@ $$$ ")" >> pair (d - 1)) ||
  Scan.lift ($$$ "*" --| Scan.ahead (~$$$ ")")) ||
  Scan.lift (Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s)) >> single;

val scan_cmts = Scan.pass 0 (Scan.repeats scan_cmt);

in

fun scan_comment err_prefix =
  Scan.ahead ($$ "(" -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$$ "(" @@@ $$$ "*" @@@ scan_cmts @@@ $$$ "*" @@@ $$$ ")");

fun scan_comment_body err_prefix =
  Scan.ahead ($$ "(" -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$ "(" |-- $$ "*" |-- scan_cmts --| $$ "*" --| $$ ")");

val recover_comment =
  $$$ "(" @@@ $$$ "*" @@@ scan_cmts;

end;


(* source *)

fun source pos =
  Source.source' pos Symbol.stopper (Scan.bulk (Scan.depend (fn pos =>
    Scan.one Symbol.not_eof >> (fn s => (Position.symbol s pos, (s, pos))))));


(* compact representation -- with Symbol.DEL padding *)

type text = string;

fun pad [] = []
  | pad [(s, _)] = [s]
  | pad ((s1, pos1) :: (rest as (_, pos2) :: _)) =
      let
        val end_pos1 = Position.symbol s1 pos1;
        val d = Int.max (0, the_default 0 (Position.distance_of (end_pos1, pos2)));
      in s1 :: replicate d Symbol.DEL @ pad rest end;

val implode = implode o pad;

fun implode_range (pos1, pos2) syms =
  let val syms' = (("", pos1) :: syms @ [("", pos2)])
  in (implode syms', range syms') end;

local

fun rev_explode (str, pos) =
  fold (fn s => fn (res, p) => ((s, p) :: res, Position.symbol s p))
    (Symbol.explode str) ([], Position.no_range_position pos)
  |> #1;

in

fun explode_deleted arg =
  fold (fn (s, p) => s = Symbol.DEL ? cons p) (rev_explode arg) [];

fun explode arg =
  fold (fn (s, p) => s <> Symbol.DEL ? cons (s, p)) (rev_explode arg) [];

fun explode0 str = explode (str, Position.none);

end;


(* identifiers *)

local

val letter = Scan.one (symbol #> Symbol.is_letter);
val letdigs1 = Scan.many1 (symbol #> Symbol.is_letdig);

val sub = Scan.one (symbol #> (fn s => s = "\<^sub>"));

in

val scan_ident = letter ::: Scan.repeats (letdigs1 || sub ::: letdigs1);

end;

fun is_identifier s =
  Symbol.is_ascii_identifier s orelse
    (case try (Scan.finite stopper scan_ident) (explode0 s) of
      SOME (_, []) => true
    | _ => false);


(* numerals *)

val scan_nat = Scan.many1 (Symbol.is_digit o symbol);
val scan_float = scan_nat @@@ $$$ "." @@@ scan_nat;

end;

structure Basic_Symbol_Pos =   (*not open by default*)
struct
  val $$ = Symbol_Pos.$$;
  val ~$$ = Symbol_Pos.~$$;
  val $$$ = Symbol_Pos.$$$;
  val ~$$$ = Symbol_Pos.~$$$;
end;

type 'a scanner = 'a Symbol_Pos.scanner;
