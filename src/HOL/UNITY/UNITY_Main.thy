(*  Title:      HOL/UNITY/UNITY_Main.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge
*)

header{*Comprehensive UNITY Theory*}

theory UNITY_Main = Detects + PPROD + Follows + ProgressSets
files "UNITY_tactics.ML":

method_setup constrains = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts => 
            gen_constrains_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt) 1)) *}
    "for proving safety properties"

method_setup ensures_tac = {*
    fn args => fn ctxt =>
        Method.goal_args' (Scan.lift Args.name) 
           (gen_ensures_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt))
           args ctxt *}
    "for proving progress properties"

end
