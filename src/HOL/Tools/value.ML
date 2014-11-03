(*  Title:      HOL/Tools/value.ML
    Author:     Florian Haftmann, TU Muenchen

Generic value command for arbitrary evaluators, with default using nbe or SML.
*)

signature VALUE =
sig
  val value: Proof.context -> term -> term
  val value_select: string -> Proof.context -> term -> term
  val value_cmd: string option -> string list -> string -> Toplevel.state -> unit
  val add_evaluator: string * (Proof.context -> term -> term) -> theory -> theory
end;

structure Value : VALUE =
struct

fun default_value ctxt t =
  if null (Term.add_frees t [])
  then case try (Code_Evaluation.dynamic_value_strict ctxt) t of
    SOME t' => t'
  | NONE => Nbe.dynamic_value ctxt t
  else Nbe.dynamic_value ctxt t;

structure Evaluator = Theory_Data
(
  type T = (string * (Proof.context -> term -> term)) list;
  val empty = [("default", default_value)];
  val extend = I;
  fun merge data : T = AList.merge (op =) (K true) data;
)

val add_evaluator = Evaluator.map o AList.update (op =);

fun value_select name ctxt =
  case AList.lookup (op =) (Evaluator.get (Proof_Context.theory_of ctxt)) name
   of NONE => error ("No such evaluator: " ^ name)
    | SOME f => f ctxt;

fun value ctxt =
  let
    val evaluators = Evaluator.get (Proof_Context.theory_of ctxt)
  in
    if null evaluators
    then error "No evaluators"
    else (snd o snd o split_last) evaluators ctxt
  end;

fun value_maybe_select some_name =
  case some_name
    of NONE => value
     | SOME name => value_select name;
  
fun value_cmd some_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = value_maybe_select some_name ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.xname --| @{keyword ")"})) [];

val opt_evaluator =
  Scan.option (@{keyword "["} |-- Parse.xname --| @{keyword "]"})
  
val _ =
  Outer_Syntax.command @{command_spec "value"} "evaluate and print term"
    (opt_evaluator -- opt_modes -- Parse.term
      >> (fn ((some_name, modes), t) => Toplevel.keep (value_cmd some_name modes t)));

val _ = Context.>> (Context.map_theory
  (Thy_Output.antiquotation @{binding value}
    (Scan.lift opt_evaluator -- Term_Style.parse -- Args.term)
    (fn {source, context, ...} => fn ((some_name, style), t) => Thy_Output.output context
      (Thy_Output.maybe_pretty_source Thy_Output.pretty_term context source
        [style (value_maybe_select some_name context t)]))
  #> add_evaluator ("simp", Code_Simp.dynamic_value)
  #> add_evaluator ("nbe", Nbe.dynamic_value)
  #> add_evaluator ("code", Code_Evaluation.dynamic_value_strict))
);

end;
