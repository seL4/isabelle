(*  Title:      HOL/Eisbach/Eisbach.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Main entry point for Eisbach proof method language.
*)

theory Eisbach
imports Main
keywords
  "method" :: thy_decl and
  "conclusion"
  "premises"
  "declares"
  "methods"
  "\<bar>" "\<Rightarrow>"
  "uses"
begin

ML_file "parse_tools.ML"
ML_file "eisbach_rule_insts.ML"
ML_file "method_closure.ML"
ML_file "match_method.ML"
ML_file "eisbach_antiquotations.ML"

(* FIXME reform Isabelle/Pure attributes to make this work by default *)
setup \<open>
  fold (Method_Closure.wrap_attribute true)
    [@{binding intro}, @{binding elim}, @{binding dest}, @{binding simp}] #>
  fold (Method_Closure.wrap_attribute false)
    [@{binding THEN}, @{binding OF}, @{binding rotated}, @{binding simplified}]
\<close>

method solves methods m = (m; fail)

end
