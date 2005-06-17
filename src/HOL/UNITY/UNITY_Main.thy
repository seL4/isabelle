(*  Title:      HOL/UNITY/UNITY_Main.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge
*)

header{*Comprehensive UNITY Theory*}

theory UNITY_Main imports Detects PPROD Follows ProgressSets
uses "UNITY_tactics.ML" begin

method_setup safety = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts => 
            gen_constrains_tac (local_clasimpset_of ctxt) 1)) *}
    "for proving safety properties"

method_setup ensures_tac = {*
    fn args => fn ctxt =>
        Method.goal_args' (Scan.lift Args.name) 
           (gen_ensures_tac (local_clasimpset_of ctxt))
           args ctxt *}
    "for proving progress properties"

end
