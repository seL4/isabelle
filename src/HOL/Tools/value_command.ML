(*  Title:      HOL/Tools/value_command.ML
    Author:     Florian Haftmann, TU Muenchen

Generic value command for arbitrary evaluators, with default using nbe or SML.
*)

signature VALUE_COMMAND =
sig
  val value: Proof.context -> term -> term
  val value_select: string -> Proof.context -> term -> term
  val value_cmd: xstring -> string list -> string -> Toplevel.state -> unit
  val add_evaluator: binding * (Proof.context -> term -> term) 
    -> theory -> string * theory
end;

structure Value_Command : VALUE_COMMAND =
struct

structure Evaluators = Theory_Data
(
  type T = (Proof.context -> term -> term) Name_Space.table;
  val empty = Name_Space.empty_table "evaluator";
  val extend = I;
  val merge = Name_Space.merge_tables;
)

fun add_evaluator (b, evaluator) thy =
  let
    val (name, tab') = Name_Space.define (Context.Theory thy) true
      (b, evaluator) (Evaluators.get thy);
    val thy' = Evaluators.put tab' thy;
  in (name, thy') end;

fun intern_evaluator ctxt raw_name =
  if raw_name = "" then ""
  else Name_Space.intern (Name_Space.space_of_table
    (Evaluators.get (Proof_Context.theory_of ctxt))) raw_name;

fun default_value ctxt t =
  if null (Term.add_frees t [])
  then Code_Evaluation.dynamic_value_strict ctxt t
  else Nbe.dynamic_value ctxt t;

fun value_select name ctxt =
  if name = ""
  then default_value ctxt
  else Name_Space.get (Evaluators.get (Proof_Context.theory_of ctxt)) name ctxt;

val value = value_select "";

fun value_cmd raw_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val name = intern_evaluator ctxt raw_name;
    val t = Syntax.read_term ctxt raw_t;
    val t' = value_select name ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Proof_Context.augment t' ctxt;
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val opt_evaluator =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "";
  
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>value\<close> "evaluate and print term"
    (opt_evaluator -- opt_modes -- Parse.term
      >> (fn ((name, modes), t) => Toplevel.keep (value_cmd name modes t)));

val _ = Theory.setup
  (Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>value\<close>
    (Scan.lift opt_evaluator -- Term_Style.parse -- Args.term)
    (fn ctxt => fn ((name, style), t) =>
      Document_Output.pretty_term ctxt (style (value_select name ctxt t)))
  #> add_evaluator (\<^binding>\<open>simp\<close>, Code_Simp.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>nbe\<close>, Nbe.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>code\<close>, Code_Evaluation.dynamic_value_strict) #> snd);

end;
