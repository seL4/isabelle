(*  Title:      Pure/ML/ml_init.ML
    Author:     Makarius

Initial ML environment.
*)

val seconds = Time.fromReal;

val _ =
  List.app ML_Name_Space.forget_val
    ["isSome", "getOpt", "valOf", "foldl", "foldr", "print", "explode", "concat"];

val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = String.concat;

val pointer_eq = PolyML.pointerEq;

val error_depth = PolyML.error_depth;

open Thread;

datatype illegal = Interrupt;

structure Basic_Exn: BASIC_EXN = Exn;
open Basic_Exn;

structure String =
struct
  open String;
  fun substring (s, i, n) =
    if n = 1 then String.str (String.sub (s, i))
    else String.substring (s, i, n);
end;
