(*  Title:      HOL/Tools/datatype_hooks.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Hooks for datatype introduction.
*)

signature DATATYPE_HOOKS =
sig
  type hook = string list -> theory -> theory
  val add: hook -> theory -> theory
  val all: hook
end;

structure DatatypeHooks : DATATYPE_HOOKS =
struct

type hook = string list -> theory -> theory;

structure DatatypeHooksData = TheoryDataFun
(
  type T = (serial * hook) list;
  val empty = [];
  val copy = I;
  val extend = I;
  fun merge _ hooks : T = AList.merge (op =) (K true) hooks;
);

fun add hook =
  DatatypeHooksData.map (cons (serial (), hook));

fun all dtcos thy =
  fold_rev (fn (_, f) => f dtcos) (DatatypeHooksData.get thy) thy;

end;
