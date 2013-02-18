(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_PROOF =
sig
	type label = string * int
  val no_label : label
  type facts = label list * string list
  val no_facts : facts

  datatype isar_qualifier = Show | Then

  datatype isar_step =
    Fix of (string * typ) list |
    Let of term * term |
    Assume of label * term |
    Obtain of
      isar_qualifier list * (string * typ) list * label * term * byline |
    Prove of isar_qualifier list * label * term * byline
  and byline =
    By_Metis of isar_step list list * facts

  val string_for_label : label -> string
  val metis_steps_top_level : isar_step list -> int
  val metis_steps_total : isar_step list -> int
  val term_of_assm : isar_step -> term
  val term_of_prove : isar_step -> term
  val split_proof :
    isar_step list -> (string * typ) list * (label * term) list * term
end

structure Sledgehammer_Proof : SLEDGEHAMMER_PROOF =
struct

type label = string * int
val no_label = ("", ~1)
type facts = label list * string list
val no_facts = ([],[])

datatype isar_qualifier = Show | Then

datatype isar_step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Obtain of isar_qualifier list * (string * typ) list * label * term * byline |
  Prove of isar_qualifier list * label * term * byline
and byline =
  By_Metis of isar_step list list * facts

fun string_for_label (s, num) = s ^ string_of_int num

fun metis_steps_top_level proof =
  fold (fn Obtain _ => Integer.add 1 | Prove _ => Integer.add 1 | _ => I)
       proof 0
fun metis_steps_total proof =
  let
    fun add_substeps subproofs i =
      Integer.add (fold Integer.add (map metis_steps_total subproofs) i)
  in
    fold
    (fn Obtain (_, _, _, _, By_Metis (subproofs, _)) => add_substeps subproofs 1
      | Prove (_, _, _, By_Metis (subproofs, _)) => add_substeps subproofs 1
      | _ => I)
    proof 0
  end

fun term_of_assm (Assume (_, t)) = t
  | term_of_assm _ = error "sledgehammer proof: unexpected constructor"
fun term_of_prove (Prove (_, _, t, _)) = t
  | term_of_prove _ = error "sledgehammer proof: unexpected constructor"

fun split_proof proof =
  let
    fun split_step step (fixes, assms, _) =
      (case step of
        Fix xs   => (xs@fixes, assms,    step)
      | Assume a => (fixes,    a::assms, step)
      | _        => (fixes,    assms,    step))
    val (fixes, assms, concl) =
      fold split_step proof ([], [], Let (Term.dummy, Term.dummy)) (* FIXME: hack *)
  in
    (rev fixes, rev assms, term_of_prove concl)
  end

end
