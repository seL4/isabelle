(*
    Degree of polynomials
    $Id$
    written by Clemens Ballarin, started 22. 1. 1997
*)

Degree = PolyRing +

consts
  deg		:: ('a::ringS) up => nat

defs
  deg_def	"deg p == LEAST n. bound n (Rep_UP p)"

end
