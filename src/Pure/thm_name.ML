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
  val print: T -> string
  val short: T -> string
  type P = T * Position.T
  val none: P
  val list: string * Position.T -> 'a list -> (P * 'a) list
  val expr: string * Position.T -> ('a list * 'b) list -> ((P * 'a) list * 'b) list
end;

structure Thm_Name: THM_NAME =
struct

type T = string * int;
val ord = prod_ord string_ord int_ord;

structure Set = Set(type key = T val ord = ord);
structure Table = Table(Set.Key);

val empty: T = ("", 0);
fun is_empty ((a, _): T) = a = "";

fun print (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ enclose "(" ")" (string_of_int index);

fun short (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ "_" ^ string_of_int index;


type P = T * Position.T;

val none: P = (empty, Position.none);

fun list (name, pos) [thm] = [(((name, 0), pos): P, thm)]
  | list ("", pos) thms = map (fn thm => ((empty, pos), thm)) thms
  | list (name, pos) thms = map_index (fn (i, thm) => (((name, i + 1), pos), thm)) thms;

fun expr name = burrow_fst (burrow (list name));

end;
