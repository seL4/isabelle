(*  Title:      Doc/more_antiquote.ML
    Author:     Florian Haftmann, TU Muenchen

More antiquotations.
*)

signature MORE_ANTIQUOTE =
sig
  val setup: theory -> theory
end;

structure More_Antiquote : MORE_ANTIQUOTE =
struct

(* code theorem antiquotation *)

local

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;

fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

fun no_vars ctxt thm =
  let
    val ctxt' = Variable.set_body false ctxt;
    val ((_, [thm]), _) = Variable.import true [thm] ctxt';
  in thm end;

fun pretty_code_thm src ctxt raw_const =
  let
    val thy = Proof_Context.theory_of ctxt;
    val const = Code.check_const thy raw_const;
    val (_, eqngr) = Code_Preproc.obtain true thy [const] [];
    fun holize thm = @{thm meta_eq_to_obj_eq} OF [thm];
    val thms = Code_Preproc.cert eqngr const
      |> Code.equations_of_cert thy
      |> snd
      |> map_filter (fn (_, (some_thm, proper)) => if proper then some_thm else NONE)
      |> map (holize o no_vars ctxt o AxClass.overload thy);
  in Thy_Output.output ctxt (Thy_Output.maybe_pretty_source pretty_thm ctxt src thms) end;

in

val setup =
  Thy_Output.antiquotation @{binding code_thms} Args.term
    (fn {source, context, ...} => pretty_code_thm source context);

end;

end;
