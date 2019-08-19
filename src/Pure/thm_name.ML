(*  Title:      Pure/thm_name.ML
    Author:     Makarius

Systematic naming of individual theorems, as selections from multi-facts.

  (NAME, 0): the single entry of a singleton fact NAME
  (NAME, i): entry i of a non-singleton fact (1 <= i <= length)
*)

signature THM_NAME =
sig
  type T = string * int
  val ord: T * T -> order
  val print: T -> string
  val flatten: T -> string
  val make_list: string -> thm list -> (T * thm) list
end;

structure Thm_Name: THM_NAME =
struct

type T = string * int;
val ord = prod_ord string_ord int_ord;

fun print (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ enclose "(" ")" (string_of_int index);

fun flatten (name, index) =
  if name = "" orelse index = 0 then name
  else name ^ "_" ^ string_of_int index;

fun make_list name [thm: thm] = [((name, 0), thm)]
  | make_list name thms = map_index (fn (i, thm) => ((name, i + 1), thm)) thms;

end;
