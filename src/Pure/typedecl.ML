(*  Title:      Pure/typedecl.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Primitive type declarations.
*)

signature TYPEDECL =
sig
  val add: bstring * string list * mixfix -> theory -> typ * theory
  val interpretation: (string -> theory -> theory) -> theory -> theory
end

structure Typedecl: TYPEDECL =
struct

structure TypedeclInterpretation = InterpretationFun(type T = string val eq = op =);
val interpretation = TypedeclInterpretation.interpretation;

val _ = Context.add_setup TypedeclInterpretation.init;

fun add (a, vs : string list, mx) thy =
  let
    val no_typargs = if not (has_duplicates (op =) vs) then length vs
      else error ("Duplicate parameters in type declaration: " ^ quote a);
    val a' = Sign.full_name thy a;
    val T = Type (a', map (fn v => TFree (v, [])) vs);
  in
    thy
    |> Sign.add_types [(a, no_typargs, mx)]
    |> TypedeclInterpretation.data a'
    |> pair T
  end;

end;
