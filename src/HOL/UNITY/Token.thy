(*  Title:      HOL/UNITY/Token
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Token Ring.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.
*)


Token = WFair +

(*process states*)
datatype pstate = Hungry | Eating | Thinking

record state =
  token :: nat
  proc  :: nat => pstate

consts
  N :: nat	(*number of nodes in the ring*)

constdefs
  nodeOrder :: "nat => (nat*nat)set"
    "nodeOrder j == (inv_image less_than (%i. ((j+N)-i) mod N))  Int
                    (lessThan N Times lessThan N)"

  next      :: nat => nat
    "next i == (Suc i) mod N"

  HasTok :: nat => state set
    "HasTok i == {s. token s = i}"

  H :: nat => state set
    "H i == {s. proc s i = Hungry}"

  E :: nat => state set
    "E i == {s. proc s i = Eating}"

  T :: nat => state set
    "T i == {s. proc s i = Thinking}"

rules
  N_positive "0<N"

  skip "id: acts"

  TR2  "constrains acts (T i) (T i Un H i)"

  TR3  "constrains acts (H i) (H i Un E i)"

  TR4  "constrains acts (H i - HasTok i) (H i)"

  TR5  "constrains acts (HasTok i) (HasTok i Un Compl(E i))"

  TR6  "leadsTo acts (H i Int HasTok i) (E i)"

  TR7  "leadsTo acts (HasTok i) (HasTok (next i))"

end
