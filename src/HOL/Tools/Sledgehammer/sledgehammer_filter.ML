(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_filter.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's hybrid relevance filter.
*)

signature SLEDGEHAMMER_FILTER =
sig
  type stature = ATP_Problem_Generate.stature
  type relevance_fudge = Sledgehammer_Filter_Iter.relevance_fudge
  type relevance_override = Sledgehammer_Filter_Iter.relevance_override

  val relevant_facts :
    Proof.context -> real * real -> int
    -> (string * typ -> term list -> bool * term list) -> relevance_fudge
    -> relevance_override -> thm list -> term list -> term
    -> (((unit -> string) * stature) * thm) list
    -> ((string * stature) * thm) list
end;

structure Sledgehammer_Filter : SLEDGEHAMMER_FILTER =
struct

open Sledgehammer_Filter_Iter

val relevant_facts = iterative_relevant_facts

end;
