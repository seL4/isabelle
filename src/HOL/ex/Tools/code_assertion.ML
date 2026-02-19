(*  Title:      HOL/ex/Code_Assertion.thy
    Author:     Florian Haftmann, TU Muenchen
*)

signature CODE_ASSERTION =
sig
  val apply: bool Config.T
  val attribute: attribute context_parser
end;

structure Code_Assertion : CODE_ASSERTION =
struct

val apply = Attrib.setup_config_bool \<^binding>\<open>code_apply_assertion\<close> (K true);

fun assert_code_for thy target_name consts =
  (Pretty.big_list ("Asserting code generation in " ^ target_name ^ " for constant(s): ")
    (map (Pretty.str o Code.string_of_const thy) consts)
  |> Pretty.writeln;
  Code_Target.produce_code (Proof_Context.init_global thy) false consts target_name Code_Target.generatedN NONE [])

fun explicit_code_assert target_name prospective_consts = Thm.declaration_attribute
  (fn _ => Context.mapping (tap (fn thy => assert_code_for thy target_name (prospective_consts thy))) I);

fun prepare_equation thy =
  let
    val ctxt = Proof_Context.init_global thy
  in Local_Defs.meta_rewrite_rule ctxt #> Axclass.unoverload ctxt end;

fun const_for thy thm =
  Code.assert_eqn thy (prepare_equation thy thm, false)
  |> fst
  |> Thm.plain_prop_of
  |> Logic.dest_equals
  |> fst
  |> strip_comb
  |> fst
  |> dest_Const
  |> fst;

fun implicit_code_assert target_name = Thm.declaration_attribute
  (fn thm => Context.mapping (tap (fn thy => assert_code_for thy target_name [const_for thy thm])) I);

fun export_global ctxt thy =
  Variable.export_terms ctxt (Proof_Context.init_global thy);

fun prospective_check_consts ctxt ts thy =
  ts
  |> export_global ctxt thy
  |> map Logic.unvarify_types_global
  |> map (Code.check_const thy);

val prospective_const_args = Args.context :|--
  (fn ctxt => Scan.repeat1 Args.term >> prospective_check_consts ctxt);

val target_arg = Args.context :|--
  (fn ctxt => Scan.lift Args.name >> Code_Target.assert_target (Proof_Context.theory_of ctxt));

val attribute =
  (Scan.lift Args.colon |-- prospective_const_args --| Scan.lift (Args.$$$ "in") -- target_arg)
  >> (fn (prospective_consts, target_name) => explicit_code_assert target_name prospective_consts)
  || (Scan.lift (Args.$$$ "in") |-- target_arg)
     >> (fn target_name => implicit_code_assert target_name)

end
