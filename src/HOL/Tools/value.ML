(*  Title:      HOL/Tools/value.ML
    Author:     Florian Haftmann, TU Muenchen

Evaluation using nbe or SML.
*)

signature VALUE =
sig
  val value: Proof.context -> term -> term
  val value_cmd: string list -> string -> Toplevel.state -> unit
end;

structure Value : VALUE =
struct

fun value ctxt t =
  if null (Term.add_frees t [])
  then case try (Code_Evaluation.dynamic_value_strict ctxt) t of
    SOME t' => t'
  | NONE => Nbe.dynamic_value ctxt t
  else Nbe.dynamic_value ctxt t;

fun value_cmd modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = value ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.xname --| @{keyword ")"})) [];

val _ =
  Outer_Syntax.improper_command @{command_spec "value"} "evaluate and print term"
    (opt_modes -- Parse.term
      >> (fn (modes, t) => Toplevel.keep (value_cmd modes t)));

val _ = Context.>> (Context.map_theory
  (Thy_Output.antiquotation @{binding value}
    (Term_Style.parse -- Args.term)
    (fn {source, context, ...} => fn (style, t) => Thy_Output.output context
      (Thy_Output.maybe_pretty_source Thy_Output.pretty_term context source
        [style (value context t)]))));

end;
