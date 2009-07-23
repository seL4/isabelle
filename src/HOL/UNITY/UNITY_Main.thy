(*  Title:      HOL/UNITY/UNITY_Main.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge
*)

header{*Comprehensive UNITY Theory*}

theory UNITY_Main imports Detects PPROD Follows ProgressSets
uses "UNITY_tactics.ML" begin

method_setup safety = {*
    Scan.succeed (fn ctxt =>
        SIMPLE_METHOD' (constrains_tac (clasimpset_of ctxt))) *}
    "for proving safety properties"

method_setup ensures_tac = {*
  Args.goal_spec -- Scan.lift Args.name_source >>
  (fn (quant, s) => fn ctxt => SIMPLE_METHOD'' quant (ensures_tac (clasimpset_of ctxt) s))
*} "for proving progress properties"

end
