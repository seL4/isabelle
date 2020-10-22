(*  Title:      Pure/Isar/target_context.ML
    Author:     Florian Haftmann

Handling of named and nested targets at the Isar toplevel via context begin / end blocks.
*)

signature TARGET_CONTEXT =
sig
  val context_begin_named_cmd: xstring * Position.T -> theory -> local_theory
  val end_named_cmd: local_theory -> theory
  val switch_named_cmd: (xstring * Position.T) option -> Context.generic ->
    (local_theory -> Context.generic) * local_theory
  val context_begin_nested_cmd: (xstring * Position.T) list -> Element.context list ->
    Context.generic -> local_theory
  val end_nested_cmd: local_theory -> Context.generic
end;

structure Target_Context: TARGET_CONTEXT =
struct

fun context_begin_named_cmd ("-", _) thy = Named_Target.theory_init thy
  | context_begin_named_cmd target thy = Named_Target.init (Locale.check thy target) thy;

val end_named_cmd = Local_Theory.exit_global;

fun switch_named_cmd NONE (Context.Theory thy) =
      (Context.Theory o end_named_cmd, Named_Target.theory_init thy)
  | switch_named_cmd (SOME name) (Context.Theory thy) =
      (Context.Theory o end_named_cmd, context_begin_named_cmd name thy)
  | switch_named_cmd NONE (Context.Proof lthy) =
      (Context.Proof o Local_Theory.reset, lthy)
  | switch_named_cmd (SOME name) (Context.Proof lthy) =
      (Context.Proof o Named_Target.reinit lthy o end_named_cmd,
        (context_begin_named_cmd name o end_named_cmd o Local_Theory.assert_nonbrittle) lthy);

fun includes raw_incls lthy =
  Bundle.includes (map (Bundle.check lthy) raw_incls) lthy;

fun context_begin_nested_cmd raw_incls raw_elems gthy =
  gthy
  |> Context.cases Named_Target.theory_init Local_Theory.assert
  |> includes raw_incls
  |> Expression.read_declaration ([], []) I raw_elems
  |> (#4 o fst)
  |> Local_Theory.begin_nested
  |> snd;

fun end_nested_cmd lthy = 
  if Named_Target.is_theory lthy
  then Context.Theory (Local_Theory.exit_global lthy)
  else Context.Proof lthy;

end;

structure Local_Theory : LOCAL_THEORY = struct open Local_Theory; end;
