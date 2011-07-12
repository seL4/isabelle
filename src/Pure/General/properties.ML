(*  Title:      Pure/General/properties.ML
    Author:     Makarius

Property lists.
*)

signature PROPERTIES =
sig
  type entry = string * string
  type T = entry list
  val defined: T -> string -> bool
  val get: T -> string -> string option
  val get_int: T -> string -> int option
  val put: entry -> T -> T
  val put_int: string * int -> T -> T
  val remove: string -> T -> T
end;

structure Properties: PROPERTIES =
struct

type entry = string * string;
type T = entry list;

fun defined (props: T) name = AList.defined (op =) props name;

fun get (props: T) name = AList.lookup (op =) props name;
fun get_int props name = (case get props name of NONE => NONE | SOME s => Int.fromString s);

fun put entry (props: T) = AList.update (op =) entry props;
fun put_int (name, i) = put (name, signed_string_of_int i);

fun remove name (props: T) = AList.delete (op =) name props;

end;
