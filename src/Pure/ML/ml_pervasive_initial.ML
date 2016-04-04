(*  Title:      Pure/ML/ml_pervasive_initial.ML
    Author:     Makarius

Pervasive ML environment: initial setup.
*)

structure PolyML_Pretty =
struct
  datatype context = datatype PolyML.context;
  datatype pretty = datatype PolyML.pretty;
end;

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
