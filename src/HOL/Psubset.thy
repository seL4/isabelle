(*  Title:      Psubset.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The "Proper Subset" relation
*)

Psubset = Finite + 

rules   (*not allowed as "defs" because < is overloaded*)

  psubset_def    "A < B == A <= B & ~ A=B"

end
