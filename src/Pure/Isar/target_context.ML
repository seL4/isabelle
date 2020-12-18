(*  Title:      Pure/Isar/target_context.ML
    Author:     Florian Haftmann

Handling of named and nested targets at the Isar toplevel via context begin / end blocks.
*)

signature TARGET_CONTEXT =
sig
  val context_begin_named_cmd: (xstring * Position.T) list -> xstring * Position.T ->
    theory -> local_theory
  val end_named_cmd: local_theory -> Context.generic
  val switch_named_cmd: (xstring * Position.T) option -> Context.generic ->
    (local_theory -> Context.generic) * local_theory
  val context_begin_nested_cmd: (xstring * Position.T) list -> Element.context list ->
    Context.generic -> local_theory
  val end_nested_cmd: local_theory -> Context.generic
end;

structure Target_Context: TARGET_CONTEXT =
struct

fun prep_includes thy =
  map (Bundle.check (Proof_Context.init_global thy));

fun context_begin_named_cmd raw_includes ("-", _) thy =
      Named_Target.init (prep_includes thy raw_includes) "" thy
  | context_begin_named_cmd raw_includes name thy =
      Named_Target.init (prep_includes thy raw_includes) (Locale.check thy name) thy;

val end_named_cmd = Context.Theory o Local_Theory.exit_global;

fun switch_named_cmd NONE (Context.Theory thy) =
      (end_named_cmd, Named_Target.theory_init thy)
  | switch_named_cmd (SOME name) (Context.Theory thy) =
      (end_named_cmd, context_begin_named_cmd [] name thy)
  | switch_named_cmd NONE (Context.Proof lthy) =
      (Context.Proof o Local_Theory.reset, lthy)
  | switch_named_cmd (SOME name) (Context.Proof lthy) =
      (Context.Proof o Named_Target.reinit lthy o Local_Theory.exit_global,
        (context_begin_named_cmd [] name o Local_Theory.exit_global_reinitializable) lthy);

fun includes raw_includes lthy =
  Bundle.includes (map (Bundle.check lthy) raw_includes) lthy;

fun context_begin_nested_cmd raw_includes raw_elems gthy =
  gthy
  |> Context.cases Named_Target.theory_init Local_Theory.assert
  |> includes raw_includes
  |> Expression.read_declaration ([], []) I raw_elems
  |> (#4 o fst)
  |> Local_Theory.begin_nested
  |> snd;

fun end_nested_cmd lthy =
  let
    val lthy' = Local_Theory.end_nested lthy
  in
    if Named_Target.is_theory lthy'
    then Context.Theory (Local_Theory.exit_global lthy')
    else Context.Proof lthy'
  end;

end;

structure Local_Theory : LOCAL_THEORY = struct open Local_Theory; end;
