(*  Title:      Pure/General/properties.ML
    ID:         $Id$
    Author:     Makarius

Property lists.
*)

signature PROPERTIES =
sig
  type property = string * string
  type T = property list
  val defined: T -> string -> bool
  val get: T -> string -> string option
  val put: string * string -> T -> T
  val remove: string -> T -> T
end;

structure Properties: PROPERTIES =
struct

type property = string * string;
type T = property list;

fun defined (props: T) name = AList.defined (op =) props name;
fun get (props: T) name = AList.lookup (op =) props name;
fun put prop (props: T) = AList.update (op =) prop props;
fun remove name (props: T) = AList.delete (op =) name props;

end;
