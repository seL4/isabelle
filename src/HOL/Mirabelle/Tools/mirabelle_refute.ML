(*  Title:      HOL/Mirabelle/Tools/mirabelle_refute.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

structure Mirabelle_Refute : MIRABELLE_ACTION =
struct


(* FIXME:
fun refute_action args timeout {pre=st, ...} = 
  let
    val subgoal = 1
    val thy = Proof.theory_of st
    val thm = #goal (Proof.raw_goal st)

    val refute = Refute.refute_goal thy args thm
    val _ = TimeLimit.timeLimit timeout refute subgoal
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
        then SOME "no counterexample (timeout)"
        else if Substring.isSubstring "Search terminated" writ_log
        then SOME "no counterexample (normal termination)"
        else SOME "no counterexample (unknown)"
  in r end
*)

fun invoke args = I (*Mirabelle.register ("refute", refute_action args)*)

end
