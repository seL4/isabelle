(*  Title:      Pure/thm_name.ML
    Author:     Makarius

Systematic naming of individual theorems, as selections from multi-facts.

  (NAME, 0): the single entry of a singleton fact NAME
  (NAME, i): entry i of a non-singleton fact (1 <= i <= length)
*)

signature THM_NAME =
sig
  type T = string * int
  val ord: T ord
  structure Set: SET
  structure Table: TABLE
  val empty: T
  val is_empty: T -> bool
  val make_list: string * 'a list -> (T * 'a) list

  type P = T * Position.T
  val none: P
  val list: string * Position.T -> 'a list -> (P * 'a) list
  val expr: string * Position.T -> ('a list * 'b) list -> ((P * 'a) list * 'b) list

  val parse: string -> T
  val print_prefix: Context.generic -> Name_Space.T -> T -> Markup.T * string
  val print_suffix: T -> string
  val print: T -> string
  val print_pos: P -> string
  val short: T -> string
  val encode: T XML.Encode.T
  val decode: T XML.Decode.T
  val encode_pos: P XML.Encode.T
  val decode_pos: P XML.Decode.T
end;

structure Thm_Name: THM_NAME =
struct

(* type T *)

type T = string * int;
val ord = prod_ord string_ord int_ord;

structure Set = Set(type key = T val ord = ord);
structure Table = Table(Set.Key);

val empty: T = ("", 0);
fun is_empty ((a, _): T) = a = "";

fun make_list (a, [b]) = [((a, 0): T, b)]
  | make_list (a, bs) = map_index (fn (i, b) => ((a, i + 1), b)) bs;


(* type P *)

type P = T * Position.T;

val none: P = (empty, Position.none);

fun list (name, pos) [x] = [(((name, 0), pos): P, x)]
  | list ("", pos) xs = map (fn thm => ((empty, pos), thm)) xs
  | list (name, pos) xs = map_index (fn (i, thm) => (((name, i + 1), pos), thm)) xs;

fun expr name = burrow_fst (burrow (list name));


(* parse *)

local

fun is_bg c = c = #"(";
fun is_en c = c = #")";
fun is_digit c = #"0" <= c andalso c <= #"9";
fun get_digit c = Char.ord c - Char.ord #"0";

in

fun parse string =
  let
    val n = size string;
    fun char i = if 0 <= i andalso i < n then String.nth string i else #"\000";
    fun test pred i = pred (char i);

    fun scan i k m =
      let val c = char i in
        if is_digit c then scan (i - 1) (k * 10) (m + k * get_digit c)
        else if is_bg c then (String.substring (string, 0, i), m)
        else (string, 0)
      end;
  in
    if test is_en (n - 1) andalso test is_digit (n - 2)
    then scan (n - 2) 1 0
    else (string, 0)
  end;

end;


(* print *)

fun print_prefix context space ((name, _): T) =
  if name = "" then (Markup.empty, "")
  else (Name_Space.markup space name, Name_Space.extern_generic context space name);

fun print_suffix (name, index) =
  if name = "" orelse index = 0 then ""
  else enclose "(" ")" (string_of_int index);

fun print (name, index) = name ^ print_suffix (name, index);

fun print_pos (thm_name, pos) = print thm_name ^ Position.here pos;

fun short (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ "_" ^ string_of_int index;


(* XML data representation *)

val encode = let open XML.Encode in pair string int end;
val decode = let open XML.Decode in pair string int end;

val encode_pos = let open XML.Encode in pair encode (properties o Position.properties_of) end;
val decode_pos = let open XML.Decode in pair decode (Position.of_properties o properties) end;

end;
