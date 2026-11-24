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

fun eq ((x, i): T, (y, j): T) = i = j andalso x = y;

val ord = pointer_eq_ord (int_ord o apply2 snd ||| fast_string_ord o apply2 fst);

end;

structure Vartab = Table(type key = Var_Name.T val ord = Var_Name.ord);
structure Var_Graph = Graph(Vartab.Key);
