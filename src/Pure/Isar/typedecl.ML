(*  Title:      Pure/Isar/typedecl.ML
    Author:     Makarius

Type declarations (within the object logic).
*)

signature TYPEDECL =
sig
  val typedecl: binding * string list * mixfix -> theory -> typ * theory
end;

structure Typedecl: TYPEDECL =
struct

fun typedecl (b, vs, mx) thy =
  let
    val base_sort = Object_Logic.get_base_sort thy;
    val _ = has_duplicates (op =) vs andalso
      error ("Duplicate parameters in type declaration " ^ quote (Binding.str_of b));
    val name = Sign.full_name thy b;
    val n = length vs;
    val T = Type (name, map (fn v => TFree (v, [])) vs);
  in
    thy
    |> Sign.add_types [(b, n, mx)]
    |> (case base_sort of NONE => I | SOME S => AxClass.axiomatize_arity (name, replicate n S, S))
    |> pair T
  end;

end;

