(*  Title:      HOL/Eisbach/Eisbach.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Main entry point for Eisbach proof method language.
*)

theory Eisbach
imports Pure
keywords
  "method" :: thy_decl and
  "conclusion"
  "declares"
  "methods"
  "\<bar>" "\<Rightarrow>"
  "uses"
begin

ML_file "parse_tools.ML"
ML_file "method_closure.ML"
ML_file "eisbach_rule_insts.ML"
ML_file "match_method.ML"

method solves methods m = (m; fail)

method_setup use = \<open>
  Scan.lift (Parse.and_list1 Parse.thms1 --| Parse.$$$ "in") -- Method_Closure.method_text >>
    (fn (raw_args, text) => fn static_ctxt =>
      let
        (* FIXME closure *)
        val args =
          Attrib.map_facts_refs
            (map (Attrib.attribute_cmd static_ctxt)) (Proof_Context.get_fact static_ctxt)
            (map (pair (Binding.empty, [])) raw_args);
      in
        fn _ => fn (ctxt, st) =>
          let val (facts, ctxt') = ctxt |> Proof_Context.note_thmss "" args |>> maps #2
          in Method_Closure.method_evaluate text ctxt' facts (ctxt', st) end
      end)
\<close> \<open>indicate method facts and context for method expression\<close>

end
