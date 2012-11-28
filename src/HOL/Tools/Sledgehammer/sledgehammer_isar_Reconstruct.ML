(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_recontruct.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Basic data structures for representing and basic methods
for dealing with Isar proof texts.
*)

signature SLEDGEHAMMER_ISAR =
sig
	val annotate_types : Proof.context -> term -> term
end

structure Sledgehammer_Isar_Reconstruct (* : SLEDGEHAMMER_Isar *) = 
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

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover = SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end

val inc = curry op+
fun metis_steps_top_level proof = fold (fn Prove _ => inc 1 | _ => I) proof 0
fun metis_steps_recursive proof = 
  fold (fn Prove (_,_,_, By_Metis _) => inc 1
         | Prove (_,_,_, Case_Split (cases, _)) => 
           inc (fold (inc o metis_steps_recursive) cases 1)
         | _ => I) proof 0

end
