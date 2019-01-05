(*  Title:      Doc/more_antiquote.ML
    Author:     Florian Haftmann, TU Muenchen

More antiquotations (partly depending on Isabelle/HOL).
*)

structure More_Antiquote : sig end =
struct

(* class specifications *)

val _ =
  Theory.setup (Thy_Output.antiquotation_pretty \<^binding>\<open>class_spec\<close> (Scan.lift Args.name)
    (fn ctxt => fn s =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val class = Sign.intern_class thy s;
      in Pretty.chunks (Class.pretty_specification thy class) end));


(* code theorem antiquotation *)

fun no_vars ctxt thm =
  let
    val ctxt' = Variable.set_body false ctxt;
    val ((_, [thm]), _) = Variable.import true [thm] ctxt';
  in thm end;

val _ =
  Theory.setup (Thy_Output.antiquotation_pretty \<^binding>\<open>code_thms\<close> Args.term
    (fn ctxt => fn raw_const =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val const = Code.check_const thy raw_const;
        val { eqngr, ... } = Code_Preproc.obtain true { ctxt = ctxt, consts = [const], terms = [] };
        val thms = Code_Preproc.cert eqngr const
          |> Code.equations_of_cert thy
          |> snd
          |> these
          |> map_filter (fn (_, (some_thm, proper)) => if proper then some_thm else NONE)
          |> map (HOLogic.mk_obj_eq o no_vars ctxt o Axclass.overload ctxt);
      in Pretty.chunks (map (Thy_Output.pretty_thm ctxt) thms) end));

end;
