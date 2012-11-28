(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_Proof =
sig
	(* FIXME: TODO *)
end

structure Sledgehammer_Proof (* : SLEDGEHAMMER_Proof *) = 
struct

type label = string * int
type facts = label list * string list

datatype isar_qualifier = Show | Then | Ultimately

datatype isar_step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Prove of isar_qualifier list * label * term * byline
and byline =
  By_Metis of facts |
  Case_Split of isar_step list list * facts

fun string_for_label (s, num) = s ^ string_of_int num

val inc = curry op+
fun metis_steps_top_level proof = fold (fn Prove _ => inc 1 | _ => I) proof 0
fun metis_steps_recursive proof = 
  fold (fn Prove (_,_,_, By_Metis _) => inc 1
         | Prove (_,_,_, Case_Split (cases, _)) => 
           inc (fold (inc o metis_steps_recursive) cases 1)
         | _ => I) proof 0

end
