(*  Title:      Pure/General/symbol_pos.ML
    Author:     Makarius

Symbols with explicit position information.
*)

signature BASIC_SYMBOL_POS =
sig
  type T = Symbol.symbol * Position.T
  val symbol: T -> Symbol.symbol
  val $$$ : Symbol.symbol -> T list -> T list * T list
  val ~$$$ : Symbol.symbol -> T list -> T list * T list
end

signature SYMBOL_POS =
sig
  include BASIC_SYMBOL_POS
  val content: T list -> string
  val untabify_content: T list -> string
  val is_eof: T -> bool
  val stopper: T Scan.stopper
  val !!! : string -> (T list -> 'a) -> T list -> 'a
  val change_prompt: ('a -> 'b) -> 'a -> 'b
  val scan_pos: T list -> Position.T * T list
  val scan_string: T list -> (Position.T * (T list * Position.T)) * T list
  val scan_alt_string: T list -> (Position.T * (T list * Position.T)) * T list
  val scan_quoted: T list -> T list * T list
  val scan_comment: (string -> (T list -> T list * T list) -> T list -> T list * T list) ->
    T list -> T list * T list
  val scan_comment_body: (string -> (T list -> T list * T list) -> T list -> T list * T list) ->
    T list -> T list * T list
  val source: Position.T -> (Symbol.symbol, 'a) Source.source ->
    (T, Position.T * (Symbol.symbol, 'a) Source.source) Source.source
  type text = string
  val implode: T list -> text
  val range: T list -> Position.range
  val implode_range: Position.T -> Position.T -> T list -> text * Position.range
  val explode: text * Position.T -> T list
end;

structure Symbol_Pos: SYMBOL_POS =
struct

(* type T *)

type T = Symbol.symbol * Position.T;

fun symbol ((s, _): T) = s;


(* content *)

val content = implode o map symbol;


val tab_width = (8: int);

fun untabify ("\t", pos) =
      (case Position.column_of pos of
        SOME n => Symbol.spaces (tab_width - ((n - 1) mod tab_width))
      | NONE => Symbol.space)
  | untabify (s, _) = s;

val untabify_content = implode o map untabify;


(* stopper *)

fun mk_eof pos = (Symbol.eof, pos);
val eof = mk_eof Position.none;

val is_eof = Symbol.is_eof o symbol;

val stopper =
  Scan.stopper (fn [] => eof | inp => mk_eof (List.last inp |-> Position.advance)) is_eof;


(* basic scanners *)

fun !!! text scan =
  let
    fun get_pos [] = " (past end-of-text!)"
      | get_pos ((_, pos) :: _) = Position.str_of pos;

    fun err (syms, msg) =
      text ^ get_pos syms ^ " at " ^ Symbol.beginning 10 (map symbol syms) ^
      (case msg of NONE => "" | SOME s => "\n" ^ s);
  in Scan.!! err scan end;

fun change_prompt scan = Scan.prompt "# " scan;

fun $$$ s = Scan.one (fn x => symbol x = s) >> single;
fun ~$$$ s = Scan.one (fn x => symbol x <> s) >> single;

val scan_pos = Scan.ahead (Scan.one (K true)) >> (fn (_, pos): T => pos);


(* Isabelle strings *)

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
  (scan_pos --| $$$ q) -- !!! "missing quote at end of string"
    (change_prompt ((Scan.repeat (scan_str q) >> flat) -- ($$$ q |-- scan_pos)));

in

val scan_string = scan_strs "\"";
val scan_alt_string = scan_strs "`";

val scan_quoted = Scan.trace (scan_string || scan_alt_string) >> #2;

end;


(* ML-style comments *)

local

val scan_cmt =
  Scan.depend (fn (d: int) => $$$ "(" @@@ $$$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$$ "*" @@@ $$$ ")" >> pair (d - 1)) ||
  Scan.lift ($$$ "*" --| Scan.ahead (~$$$ ")")) ||
  Scan.lift (Scan.one (fn (s, _) => s <> "*" andalso Symbol.is_regular s)) >> single;

val scan_body = change_prompt (Scan.pass 0 (Scan.repeat scan_cmt >> flat));

in

fun scan_comment cut =
  $$$ "(" @@@ $$$ "*" @@@ cut "missing end of comment" (scan_body @@@ $$$ "*" @@@ $$$ ")");

fun scan_comment_body cut =
  $$$ "(" |-- $$$ "*" |-- cut "missing end of comment" (scan_body --| $$$ "*" --| $$$ ")");

end;


(* source *)

fun source pos =
  Source.source' pos Symbol.stopper (Scan.bulk (Scan.depend (fn pos =>
    Scan.one Symbol.not_eof >> (fn s => (Position.advance s pos, (s, pos)))))) NONE;


(* compact representation -- with Symbol.DEL padding *)

type text = string;

fun pad [] = []
  | pad [(s, _)] = [s]
  | pad ((s1, pos1) :: (rest as (s2, pos2) :: _)) =
      let
        val end_pos1 = Position.advance s1 pos1;
        val d = Int.max (0, Position.distance_of end_pos1 pos2);
      in s1 :: replicate d Symbol.DEL @ pad rest end;

val implode = implode o pad;

fun range (syms as (_, pos) :: _) =
      let val pos' = List.last syms |-> Position.advance
      in Position.range pos pos' end
  | range [] = Position.no_range;

fun implode_range pos1 pos2 syms =
  let val syms' = (("", pos1) :: syms @ [("", pos2)])
  in (implode syms', range syms') end;

fun explode (str, pos) =
  fold_map (fn s => fn p => ((s, p), (Position.advance s p)))
    (Symbol.explode str) (Position.reset_range pos)
  |> #1 |> filter_out (fn (s, _) => s = Symbol.DEL);

end;

structure Basic_Symbol_Pos: BASIC_SYMBOL_POS = Symbol_Pos;   (*not open by default*)

