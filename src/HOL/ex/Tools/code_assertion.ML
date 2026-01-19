(*  Title:      HOL/ex/Code_Assertion.thy
    Author:     Florian Haftmann, TU Muenchen
*)

signature CODE_ASSERTION =
sig
  val apply: bool Config.T
end;

structure Code_Assertion : CODE_ASSERTION =
struct

val apply = Attrib.setup_config_bool \<^binding>\<open>code_apply_assertion\<close> (K true);

fun assert_code_for thy target_name consts =
  Code_Target.produce_code (Proof_Context.init_global thy) false consts target_name Code_Target.generatedN NONE []

fun assert_code raw_target raw_ts lthy =
  let
    val target_name = Code_Target.assert_target (Proof_Context.theory_of lthy) raw_target;
    val ts = Syntax.read_terms lthy raw_ts;
  in
    lthy
    |> Config.get lthy apply ? Local_Theory.declaration
        {syntax = false, pervasive = false, pos = \<^here>}
        (fn phi => Context.mapping
          (tap (fn thy => assert_code_for thy target_name
            (map (Code.check_const thy o Logic.unvarify_global o Morphism.term phi) ts)))
          I)
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>code_assertion\<close>
    "check code generation for each global interpretation using the given definitions and target language"
    (Scan.repeat1 Parse.term --| \<^keyword>\<open>in\<close> -- Parse.name
      >> (fn (raw_ts, raw_target) => assert_code raw_target raw_ts));

end