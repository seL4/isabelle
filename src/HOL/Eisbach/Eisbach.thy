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
  Attrib.thms -- (Scan.lift @{keyword "in"} |-- Method_Closure.method_text) >>
    (fn (thms, text) => fn ctxt => fn _ => Method_Closure.method_evaluate text ctxt thms)
\<close> \<open>indicate method facts and context for method expression\<close>

end
