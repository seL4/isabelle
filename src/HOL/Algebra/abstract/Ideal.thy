(*
    Ideals for commutative rings
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

Ideal = Ring +

consts
  ideal_of	:: ('a::ringS) set => 'a set
  is_ideal	:: ('a::ringS) set => bool
  is_pideal	:: ('a::ringS) set => bool

defs
  is_ideal_def	"is_ideal I == (ALL a: I. ALL b: I. a + b : I) &
                               (ALL a: I. - a : I) & 0 : I &
                               (ALL a: I. ALL r. a * r : I)"
  ideal_of_def	"ideal_of S == Inter {I. is_ideal I & S <= I}"
  is_pideal_def	"is_pideal I == (EX a. I = ideal_of {a})"

(* Principle ideal domains *)

axclass
  pid < domain

  pid_ax	"is_ideal I ==> is_pideal I"

end