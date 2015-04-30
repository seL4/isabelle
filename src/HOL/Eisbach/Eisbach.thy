(*  Title:      Eisbach.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Main entry point for Eisbach proof method language.
*)

theory Eisbach
imports Pure
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
attribute_setup THEN =
  \<open>Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm >> (fn (i, B) =>
    Method_Closure.free_aware_rule_attribute [B] (fn _ => fn A => A RSN (i, B)))\<close>
  "resolution with rule"

attribute_setup OF =
  \<open>Attrib.thms >> (fn Bs =>
    Method_Closure.free_aware_rule_attribute Bs (fn _ => fn A => A OF Bs))\<close>
  "rule resolved with facts"

attribute_setup rotated =
  \<open>Scan.lift (Scan.optional Parse.int 1 >> (fn n =>
    Method_Closure.free_aware_rule_attribute [] (fn _ => rotate_prems n)))\<close>
  "rotated theorem premises"

method solves methods m = (m; fail)

end
