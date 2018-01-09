(*  Title:      Doc/more_antiquote.ML
    Author:     Florian Haftmann, TU Muenchen

More antiquotations (partly depending on Isabelle/HOL).
*)

structure More_Antiquote : sig end =
struct

(* class specifications *)

local

fun class_spec ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt;
    val class = Sign.intern_class thy s;
  in Thy_Output.output ctxt (Class.pretty_specification thy class) end;

in

val _ =
  Theory.setup (Document_Antiquotation.setup @{binding class_spec} (Scan.lift Args.name)
    (fn {context, ...} => class_spec context));

end;


(* code theorem antiquotation *)

local

fun no_vars ctxt thm =
  let
    val ctxt' = Variable.set_body false ctxt;
    val ((_, [thm]), _) = Variable.import true [thm] ctxt';
  in thm end;

fun pretty_code_thm ctxt raw_const =
  let
    val thy = Proof_Context.theory_of ctxt;
    val const = Code.check_const thy raw_const;
    val { eqngr, ... } = Code_Preproc.obtain true { ctxt = ctxt, consts = [const], terms = [] };
    fun holize thm = @{thm meta_eq_to_obj_eq} OF [thm];
    val thms = Code_Preproc.cert eqngr const
      |> Code.equations_of_cert thy
      |> snd
      |> these
      |> map_filter (fn (_, (some_thm, proper)) => if proper then some_thm else NONE)
      |> map (holize o no_vars ctxt o Axclass.overload ctxt);
  in Thy_Output.output ctxt (map (Thy_Output.pretty_thm ctxt) thms) end;

in

val _ =
  Theory.setup (Document_Antiquotation.setup @{binding code_thms} Args.term
    (fn {context, ...} => pretty_code_thm context));

end;

end;
