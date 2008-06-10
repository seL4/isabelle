(*  Title:      Pure/Isar/instance.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Wrapper for instantiation command.
*)

signature INSTANCE =
sig
  val instantiation_cmd: xstring list * sort * xstring -> theory -> local_theory
end;

structure Instance : INSTANCE =
struct

fun read_multi_arity thy (raw_tycos, raw_sorts, raw_sort) =
  let
    val all_arities = map (fn raw_tyco => Sign.read_arity thy
      (raw_tyco, raw_sorts, raw_sort)) raw_tycos;
    val tycos = map #1 all_arities;
    val (_, sorts, sort) = hd all_arities;
    val vs = Name.names Name.context Name.aT sorts;
  in (tycos, vs, sort) end;

fun instantiation_cmd raw_arities thy =
  TheoryTarget.instantiation (read_multi_arity thy raw_arities) thy;

end;
