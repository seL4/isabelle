(*  Title:      Pure/Isar/typedecl.ML
    Author:     Makarius

Type declarations (with object-logic arities) and type abbreviations.
*)

signature TYPEDECL =
sig
  val read_constraint: Proof.context -> string option -> sort
  val basic_typedecl: {final: bool} -> binding * int * mixfix ->
    local_theory -> string * local_theory
  val typedecl: {final: bool} -> binding * (string * sort) list * mixfix ->
    local_theory -> typ * local_theory
  val typedecl_global: {final: bool} -> binding * (string * sort) list * mixfix ->
    theory -> typ * theory
  val abbrev: binding * string list * mixfix -> typ -> local_theory -> string * local_theory
  val abbrev_cmd: binding * string list * mixfix -> string -> local_theory -> string * local_theory
  val abbrev_global: binding * string list * mixfix -> typ -> theory -> string * theory
end;

structure Typedecl: TYPEDECL =
struct

(* constraints *)

fun read_constraint _ NONE = dummyS
  | read_constraint ctxt (SOME s) = Syntax.read_sort ctxt s;


(* primitives *)

fun basic_decl decl (b, n, mx) lthy =
  let val name = Local_Theory.full_name lthy b in
    lthy
    |> Local_Theory.background_theory (decl name)
    |> Local_Theory.type_notation true Syntax.mode_default [(Type (name, replicate n dummyT), mx)]
    |> Local_Theory.type_alias b name
    |> pair name
  end;


(* global type -- without dependencies on type parameters of the context *)

fun global_type lthy (b, raw_args) =
  let
    fun err msg = error (msg ^ " in type declaration " ^ Binding.print b);

    val _ = has_duplicates (eq_fst op =) raw_args andalso err "Duplicate parameters";
    val args = map (TFree o Proof_Context.check_tfree lthy) raw_args;
    val T = Type (Local_Theory.full_name lthy b, args);

    val bad_args =
      Term.dest_Type_args (Logic.type_map (singleton (Variable.polymorphic lthy)) T)
      |> filter_out Term.is_TVar;
    val _ = null bad_args orelse
      err ("Locally fixed type arguments " ^
        commas_quote (map (Syntax.string_of_typ lthy) bad_args));
  in T end;

fun final_type (b, n) lthy =
  let
    val c = Local_Theory.full_name lthy b;
    val args = map (fn a => TFree (a, [])) (Name.invent_global_types n);
  in
    Local_Theory.background_theory
      (Theory.add_deps (Proof_Context.defs_context lthy) "" (Theory.type_dep (c, args)) []) lthy
  end;

fun basic_typedecl {final} (b, n, mx) lthy =
  lthy
  |> basic_decl (fn name =>
    Sign.add_type lthy (b, n, NoSyn) #>
    (case Object_Logic.get_base_sort lthy of
      SOME S => Axclass.arity_axiomatization (name, replicate n S, S)
    | NONE => I)) (b, n, mx)
  ||> final ? final_type (b, n);


(* type declarations *)

fun typedecl {final} (b, raw_args, mx) lthy =
  let val T = global_type lthy (b, raw_args) in
    lthy
    |> basic_typedecl {final = final} (b, length raw_args, mx)
    |> snd
    |> Variable.declare_typ T
    |> pair T
  end;

fun typedecl_global {final} decl =
  Named_Target.theory_map_result Morphism.typ (typedecl {final = final} decl);


(* type abbreviations *)

local

fun gen_abbrev prep_typ (b, vs, mx) raw_rhs lthy =
  let
    val Type (name, _) = global_type lthy (b, map (rpair dummyS) vs);
    val rhs = prep_typ b lthy raw_rhs
      handle ERROR msg => cat_error msg ("in type abbreviation " ^ Binding.print b);
  in
    lthy
    |> basic_decl (fn _ => Sign.add_type_abbrev lthy (b, vs, rhs)) (b, length vs, mx)
    |> snd
    |> pair name
  end;

fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if not (null ignored) andalso Context_Position.is_visible ctxt then
        warning
          ("Ignoring sort constraints in type variables(s): " ^
            commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
            "\nin type abbreviation " ^ Binding.print b)
      else ();
  in rhs end;

in

val abbrev = gen_abbrev (K Proof_Context.cert_typ_syntax);
val abbrev_cmd = gen_abbrev read_abbrev;

end;

fun abbrev_global decl rhs =
  Named_Target.theory_map_result (K I) (abbrev decl rhs);

end;
