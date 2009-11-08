(*  Title:      Pure/Tools/value.ML
    Author:     Florian Haftmann, TU Muenchen

Generic value command for arbitrary evaluators.
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

structure Evaluator = Theory_Data
(
  type T = (string * (Proof.context -> term -> term)) list;
  val empty = [];
  val extend = I;
  fun merge data : T = AList.merge (op =) (K true) data;
)

val add_evaluator = Evaluator.map o AList.update (op =);

fun value_select name ctxt =
  case AList.lookup (op =) (Evaluator.get (ProofContext.theory_of ctxt)) name
   of NONE => error ("No such evaluator: " ^ name)
    | SOME f => f ctxt;

fun value ctxt t = let val evaluators = Evaluator.get (ProofContext.theory_of ctxt)
  in if null evaluators then error "No evaluators"
  else let val (evaluators, (_, evaluator)) = split_last evaluators
    in case get_first (fn (_, f) => try (f ctxt) t) evaluators
     of SOME t' => t'
      | NONE => evaluator ctxt t
  end end;

fun value_cmd some_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = case some_name
     of NONE => value ctxt t
      | SOME name => value_select name ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ = OuterSyntax.improper_command "value" "evaluate and print term" K.diag
  (Scan.option (P.$$$ "[" |-- P.xname --| P.$$$ "]") -- opt_modes -- P.term
    >> (fn ((some_name, modes), t) => Toplevel.no_timing o Toplevel.keep
        (value_cmd some_name modes t)));

end; (*local*)

end;
