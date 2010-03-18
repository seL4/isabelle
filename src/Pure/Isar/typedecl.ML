(*  Title:      Pure/Isar/typedecl.ML
    Author:     Makarius

Type declarations (within the object logic).
*)

signature TYPEDECL =
sig
  val predeclare_constraints: binding * (string * sort) list * mixfix ->
    local_theory -> string * local_theory
  val typedecl: binding * (string * sort) list * mixfix -> local_theory -> typ * local_theory
  val typedecl_global: binding * (string * sort) list * mixfix -> theory -> typ * theory
end;

structure Typedecl: TYPEDECL =
struct

(* primitives *)

fun object_logic_arity name thy =
  (case Object_Logic.get_base_sort thy of
    NONE => thy
  | SOME S => AxClass.axiomatize_arity (name, replicate (Sign.arity_number thy name) S, S) thy);

fun basic_typedecl (b, n, mx) lthy =
  let val name = Local_Theory.full_name lthy b in
    lthy
    |> Local_Theory.theory (Sign.add_types [(b, n, NoSyn)] #> object_logic_arity name)
    |> Local_Theory.type_notation true Syntax.mode_default [(Type (name, replicate n dummyT), mx)]
    |> Local_Theory.type_alias b name
    |> pair name
  end;


(* syntactic version -- useful for internalizing additional types/terms beforehand *)

fun predeclare_constraints (b, raw_args, mx) =
  basic_typedecl (b, length raw_args, mx) ##>
  fold (Variable.declare_constraints o Logic.mk_type o TFree) raw_args;


(* regular version -- without dependencies on type parameters of the context *)

fun typedecl (b, raw_args, mx) lthy =
  let
    fun err msg = error (msg ^ " in type declaration " ^ quote (Binding.str_of b));

    val _ = has_duplicates (eq_fst op =) raw_args andalso err "Duplicate parameters";
    val args = raw_args
      |> map (fn (a, S) => (a, if S = dummyS then ProofContext.default_sort lthy (a, ~1) else S));
    val T = Type (Local_Theory.full_name lthy b, map TFree args);

    val bad_args =
      #2 (Term.dest_Type (Logic.type_map (singleton (Variable.polymorphic lthy)) T))
      |> filter_out Term.is_TVar;
    val _ = not (null bad_args) andalso
      err ("Locally fixed type arguments " ^
        commas_quote (map (Syntax.string_of_typ lthy) bad_args));
  in
    lthy
    |> basic_typedecl (b, length args, mx)
    |> snd
    |> Variable.declare_typ T
    |> pair T
  end;

fun typedecl_global decl =
  Theory_Target.init NONE
  #> typedecl decl
  #> Local_Theory.exit_result_global Morphism.typ;

end;

