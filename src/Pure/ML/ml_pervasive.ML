(*  Title:      Pure/ML/ml_pervasive.ML
    Author:     Makarius

Pervasive ML environment.
*)

val seconds = Time.fromReal;

val _ =
  List.app ML_Name_Space.forget_val
    ["isSome", "getOpt", "valOf", "foldl", "foldr", "print", "explode", "concat"];

val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = SML90.implode;

val pointer_eq = PolyML.pointerEq;

val error_depth = PolyML.error_depth;

open Thread;
