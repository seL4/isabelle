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

end
