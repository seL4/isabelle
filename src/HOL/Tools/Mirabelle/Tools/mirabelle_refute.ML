(* Title:  mirabelle_refute.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

structure Mirabelle_Refute : MIRABELLE_ACTION =
struct


fun refute_action args {pre=st, ...} = 
  let
    val subgoal = 0
    val thy     = Proof.theory_of st
    val thm = goal_thm_of st

    val _ = Refute.refute_subgoal thy args thm subgoal
  in
    val writ_log = Substring.full (the (Symtab.lookup tab "writeln"))
    val warn_log = Substring.full (the (Symtab.lookup tab "warning"))

    val r =
      if Substring.isSubstring "model found" writ_log
      then
        if Substring.isSubstring "spurious" warn_log
        then SOME "potential counterexample"
        else SOME "real counterexample (bug?)"
      else
        if Substring.isSubstring "time limit" writ_log
        then SOME "no counterexample (time out)"
        else if Substring.isSubstring "Search terminated" writ_log
        then SOME "no counterexample (normal termination)"
        else SOME "no counterexample (unknown)"
  in r end

fun invoke args = Mirabelle.register ("refute", refute_action args)

end
