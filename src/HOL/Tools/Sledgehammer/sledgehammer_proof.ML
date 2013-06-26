(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_PROOF =
sig
  type label = string * int
  type facts = label list * string list (* local & global *)

  datatype isar_qualifier = Show | Then

  datatype fix = Fix of (string * typ) list
  datatype assms = Assume of (label * term) list

  datatype isar_proof = 
    Proof of fix * assms * isar_step list
  and isar_step =
    Let of term * term |
    (* for |fix|>0, this is an obtain step *)
    Prove of isar_qualifier list * fix * label * term * byline
  and byline =
    By_Metis of isar_proof list * facts

  val no_label : label
  val no_facts : facts

  val string_of_label : label -> string
  val fix_of_proof : isar_proof -> fix
  val assms_of_proof : isar_proof -> assms
  val steps_of_proof : isar_proof -> isar_step list

  val label_of_step : isar_step -> label option
  val byline_of_step : isar_step -> byline option

  val add_metis_steps_top_level : isar_step list -> int -> int
  val add_metis_steps : isar_step list -> int -> int
end

structure Sledgehammer_Proof : SLEDGEHAMMER_PROOF =
struct

type label = string * int
type facts = label list * string list

datatype isar_qualifier = Show | Then

datatype fix = Fix of (string * typ) list
datatype assms = Assume of (label * term) list

datatype isar_proof = 
  Proof of fix * assms * isar_step list
and isar_step =
  Let of term * term |
  (* for |fix|>0, this is an obtain step *)
  Prove of isar_qualifier list * fix * label * term * byline
and byline =
  By_Metis of isar_proof list * facts

val no_label = ("", ~1)
val no_facts = ([],[])

fun string_of_label (s, num) = s ^ string_of_int num

fun fix_of_proof (Proof (fix, _, _)) = fix
fun assms_of_proof (Proof (_, assms, _)) = assms
fun steps_of_proof (Proof (_, _, steps)) = steps

fun label_of_step (Prove (_, _, l, _, _)) = SOME l
  | label_of_step _ = NONE

fun byline_of_step (Prove (_, _, _, _, byline)) = SOME byline
  | byline_of_step _ = NONE

val add_metis_steps_top_level =
  fold (byline_of_step #> (fn SOME (By_Metis _) => Integer.add 1 | _ => I))

fun add_metis_steps steps =
  fold (byline_of_step 
        #> (fn SOME (By_Metis (subproofs, _)) =>
                Integer.add 1 #> add_substeps subproofs
             | _ => I)) steps
and add_substeps subproofs = fold (steps_of_proof #> add_metis_steps) subproofs

end
