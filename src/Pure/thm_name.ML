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

  type P = T * Position.T
  val none: P
  val list: string * Position.T -> 'a list -> (P * 'a) list
  val expr: string * Position.T -> ('a list * 'b) list -> ((P * 'a) list * 'b) list

  val print_prefix: Context.generic -> Name_Space.T -> T -> Markup.T * string
  val print_suffix: T -> string
  val print: T -> string
  val short: T -> string
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


(* type P *)

type P = T * Position.T;

val none: P = (empty, Position.none);

fun list (name, pos) [x] = [(((name, 0), pos): P, x)]
  | list ("", pos) xs = map (fn thm => ((empty, pos), thm)) xs
  | list (name, pos) xs = map_index (fn (i, thm) => (((name, i + 1), pos), thm)) xs;

fun expr name = burrow_fst (burrow (list name));


(* output *)

fun print_prefix context space ((name, _): T) =
  if name = "" then (Markup.empty, "")
  else (Name_Space.markup space name, Name_Space.extern_generic context space name);

fun print_suffix (name, index) =
  if name = "" orelse index = 0 then ""
  else enclose "(" ")" (string_of_int index);

fun print (name, index) = name ^ print_suffix (name, index);

fun short (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ "_" ^ string_of_int index;

end;
