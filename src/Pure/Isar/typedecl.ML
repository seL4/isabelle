(*  Title:      Pure/Isar/typedecl.ML
    Author:     Makarius

Type declarations (within the object logic).
*)

signature TYPEDECL =
sig
  val typedecl: binding * string list * mixfix -> local_theory -> typ * local_theory
  val typedecl_global: binding * string list * mixfix -> theory -> typ * theory
end;

structure Typedecl: TYPEDECL =
struct

fun typedecl (b, vs, mx) lthy =
  let
    fun err msg = error (msg ^ " in type declaration " ^ quote (Binding.str_of b));
    val _ = has_duplicates (op =) vs andalso err "Duplicate parameters";

    val name = Local_Theory.full_name lthy b;
    val n = length vs;
    val args = map (fn a => TFree (a, ProofContext.default_sort lthy (a, ~1))) vs;
    val T = Type (name, args);

    val bad_args =
      #2 (Term.dest_Type (Logic.type_map (singleton (Variable.polymorphic lthy)) T))
      |> filter_out Term.is_TVar;
    val _ = not (null bad_args) andalso
      err ("Locally fixed type arguments " ^ commas_quote (map (Syntax.string_of_typ lthy) bad_args));

    val base_sort = Object_Logic.get_base_sort (ProofContext.theory_of lthy);
  in
    lthy
    |> Local_Theory.theory
      (Sign.add_types [(b, n, NoSyn)] #>
        (case base_sort of
          NONE => I
        | SOME S => AxClass.axiomatize_arity (name, replicate n S, S)))
    |> Local_Theory.checkpoint
    |> Local_Theory.type_notation true Syntax.mode_default [(T, mx)]
    |> Local_Theory.type_syntax false (fn phi =>
        let val b' = Morphism.binding phi b
        in Context.mapping (Sign.type_alias b' name) (ProofContext.type_alias b' name) end)
    |> ProofContext.type_alias b name
    |> Variable.declare_typ T
    |> pair T
  end;

fun typedecl_global decl =
  Theory_Target.init NONE
  #> typedecl decl
  #> Local_Theory.exit_result_global Morphism.typ;

end;

