(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)
*)

PPROD = Lift_prog +

constdefs

  PLam  :: ['a set, 'a => 'b program] => ('a => 'b) program
    "PLam I F == JN i:I. lift_prog i (F i)"

syntax
  "@PLam" :: [pttrn, 'a set, 'b set] => ('a => 'b) set ("(3plam _:_./ _)" 10)

translations
  "plam x:A. B"   == "PLam A (%x. B)"

end
