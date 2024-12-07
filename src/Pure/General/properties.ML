(*  Title:      Pure/General/properties.ML
    Author:     Makarius

Property lists.
*)

signature PROPERTIES =
sig
  type entry = string * string
  type T = entry list
  val print_eq: entry -> string
  val entry_ord: entry ord
  val ord: T ord
  val defined: T -> string -> bool
  val get: T -> string -> string option
  val put: entry -> T -> T
  val remove: string -> T -> T
  val make_string: string -> string -> T
  val make_int: string -> int -> T
  val get_string: T -> string -> string
  val get_bool: T -> string -> bool
  val get_int: T -> string -> int
  val get_seconds: T -> string -> Time.time
end;

structure Properties: PROPERTIES =
struct

type entry = string * string;

type T = entry list;

fun print_eq (a, b) = a ^ "=" ^ b;

val entry_ord = prod_ord string_ord string_ord;
val ord = list_ord entry_ord;

fun defined (props: T) name = AList.defined (op =) props name;
fun get (props: T) name = AList.lookup (op =) props name;
fun put entry (props: T) = AList.update (op =) entry props;
fun remove name (props: T) = AList.delete (op =) name props;

fun make_string k s = if s = "" then [] else [(k, s)];
fun make_int k i = if i = 0 then [] else [(k, Value.print_int i)];

val get_string = the_default "" oo get;

fun get_bool props name =
  (case get props name of
    NONE => false
  | SOME s => Value.parse_bool s);

fun get_int props name =
  (case get props name of
    NONE => 0
  | SOME s => Value.parse_int s);

fun get_seconds props name =
  (case get props name of
    NONE => Time.zeroTime
  | SOME s => Time.fromReal (the_default 0.0 (Real.fromString s)));

end;
