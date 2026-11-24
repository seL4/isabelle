(*  Title:      Pure/var_name.ML
    Author:     Makarius

Naming of variables: base name and index.

  (NAME, ~1): sometimes means fixed/free variable
  (NAME, i) if i >= 0: sometimes means schematic variable (for matching, unification)
*)

signature VAR_NAME =
sig
  type T = string * int
  val eq: T * T -> bool
  val ord: T ord
end;

structure Var_Name: VAR_NAME =
struct

(* type T *)

type T = string * int;

fun eq (a: T, b: T) =
  pointer_eq (a, b) orelse #2 a = #2 b andalso #1 a = #1 b;

fun ord (a: T, b: T) =
  if pointer_eq (a, b) then EQUAL
  else
    (case int_ord (#2 a, #2 b) of
      EQUAL => fast_string_ord (#1 a, #1 b)
    | ord => ord);

end;

structure Vartab = Table(type key = Var_Name.T val ord = Var_Name.ord);
structure Var_Graph = Graph(Vartab.Key);
