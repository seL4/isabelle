(*  Title:      Substitutions/setplus.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Minor additions to HOL's set theory
*)

Setplus = Set + 

rules

  ssubset_def    "A < B == A <= B & ~ A=B"

end
