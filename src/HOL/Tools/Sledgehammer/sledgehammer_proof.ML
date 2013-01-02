(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_PROOF =
sig
	type label = string * int
  type facts = label list * string list

  datatype isar_qualifier = Show | Then | Ultimately

  datatype isar_step =
    Fix of (string * typ) list |
    Let of term * term |
    Assume of label * term |
    Obtain of
      isar_qualifier list * (string * typ) list * label * term * byline |
    Prove of isar_qualifier list * label * term * byline
  and byline =
    By_Metis of facts |
    Case_Split of isar_step list list * facts

  val string_for_label : label -> string
  val metis_steps_top_level : isar_step list -> int
  val metis_steps_total : isar_step list -> int
end

structure Sledgehammer_Proof : SLEDGEHAMMER_PROOF =
struct

type label = string * int
type facts = label list * string list

datatype isar_qualifier = Show | Then | Ultimately

datatype isar_step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Obtain of isar_qualifier list * (string * typ) list * label * term * byline |
  Prove of isar_qualifier list * label * term * byline
and byline =
  By_Metis of facts |
  Case_Split of isar_step list list * facts

fun string_for_label (s, num) = s ^ string_of_int num

fun metis_steps_top_level proof =
  fold (fn Obtain _ => Integer.add 1 | Prove _ => Integer.add 1 | _ => I)
       proof 0
fun metis_steps_total proof =
  fold (fn Obtain _ => Integer.add 1
         | Prove (_, _, _, By_Metis _) => Integer.add 1
         | Prove (_, _, _, Case_Split (cases, _)) =>
           Integer.add (fold (Integer.add o metis_steps_total) cases 1)
         | _ => I) proof 0

end
