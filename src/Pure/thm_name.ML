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
  type P = T * Position.T
  val none: P
  val print: T -> string
  val short: P -> string * Position.T
  val list: string * Position.T -> 'a list -> (P * 'a) list
  val expr: string * Position.T -> ('a list * 'b) list -> ((P * 'a) list * 'b) list
end;

structure Thm_Name: THM_NAME =
struct

type T = string * int;
val ord = prod_ord string_ord int_ord;

type P = T * Position.T;

val none: P = (("", 0), Position.none);

fun print (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ enclose "(" ")" (string_of_int index);

fun short (((name, index), pos): P) =
  if name = "" orelse index = 0 then (name, pos)
  else (name ^ "_" ^ string_of_int index, pos);

fun list (name, pos) [thm] = [(((name, 0), pos): P, thm)]
  | list (name, pos) thms = map_index (fn (i, thm) => (((name, i + 1), pos), thm)) thms;

fun expr name = burrow_fst (burrow (list name));

end;
