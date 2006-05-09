(*  Title:      HOL/Tools/datatype_hooks.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Hooks for datatype introduction.
*)

signature DATATYPE_HOOKS =
sig
  type hook = string -> theory -> theory;
  val add: hook -> theory -> theory;
  val invoke: hook;
  val setup: theory -> theory;
end;

structure DatatypeHooks : DATATYPE_HOOKS =
struct


(* theory data *)

type hook = string -> theory -> theory;
datatype T = T of (serial * hook) list;

fun map_T f (T hooks) = T (f hooks);
fun merge_T pp (T hooks1, T hooks2) =
  T (AList.merge (op =) (K true) (hooks1, hooks2));

structure DatatypeHooksData = TheoryDataFun
(struct
  val name = "HOL/DatatypeHooks";
  type T = T;
  val empty = T [];
  val copy = I;
  val extend = I;
  val merge = merge_T;
  fun print _ _ = ();
end);


(* interface *)

fun add hook =
  DatatypeHooksData.map (map_T (cons (serial (), hook)));

fun invoke dtco thy =
  fold (fn (_, f) => f dtco) ((fn T hooks => hooks) (DatatypeHooksData.get thy)) thy;


(* theory setup *)

val setup = DatatypeHooksData.init;

end;

