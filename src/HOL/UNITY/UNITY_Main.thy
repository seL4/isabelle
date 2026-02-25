(*  Title:      HOL/UNITY/UNITY_Main.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge
*)

section\<open>Comprehensive UNITY Theory\<close>

theory UNITY_Main
imports Detects PPROD Follows ProgressSets
begin

ML_file \<open>UNITY_tactics.ML\<close>

method_setup safety = \<open>
    Scan.succeed (SIMPLE_METHOD' o constrains_tac)\<close>
    "for proving safety properties"

method_setup ensures_tac = \<open>
  Args.goal_spec -- Scan.lift Parse.embedded_inner_syntax >>
  (fn (quant, s) => fn ctxt => SIMPLE_METHOD'' quant (ensures_tac ctxt s))
\<close> "for proving progress properties"

setup \<open>
  Simplifier.map_theory_simpset (fn ctxt =>
    ctxt
    |> Simplifier.add_simps (make_o_equivs ctxt @{thm fst_o_funPair} @ make_o_equivs ctxt @{thm snd_o_funPair})
    |> Simplifier.add_simps (make_o_equivs ctxt @{thm fst_o_lift_map} @ make_o_equivs ctxt @{thm snd_o_lift_map}))
\<close>

end
