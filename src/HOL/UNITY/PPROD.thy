(*  Title:      HOL/UNITY/PPROD.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Abstraction over replicated components (PLam)
General products of programs (Pi operation)
*)

PPROD = Lift_prog +

constdefs

  PLam  :: "[nat set, nat => ('b * ((nat=>'b) * 'c)) program]
            => ((nat=>'b) * 'c) program"
    "PLam I F == JN i:I. lift i (F i)"

syntax
  "@PLam" :: [pttrn, nat set, 'b set] => (nat => 'b) set ("(3plam _:_./ _)" 10)

translations
  "plam x:A. B"   == "PLam A (%x. B)"

end
