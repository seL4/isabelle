(*  Title:      HOL/IOA/NTP/Multiset.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Axiomatic multisets.
Should be done as a subtype and moved to a global place.
*)

Multiset = Arith + Lemmas +

types

  'a multiset

arities

  multiset :: (term) term

consts

  "{|}"  :: 'a multiset                        ("{|}")
  addm   :: ['a multiset, 'a] => 'a multiset
  delm   :: ['a multiset, 'a] => 'a multiset
  countm :: ['a multiset, 'a => bool] => nat
  count  :: ['a multiset, 'a] => nat

rules

delm_empty_def
  "delm {|} x = {|}" 

delm_nonempty_def
  "delm (addm M x) y == (if x=y then M else addm (delm M y) x)"

countm_empty_def
   "countm {|} P == 0"

countm_nonempty_def
   "countm (addm M x) P == countm M P + (if P x then Suc 0 else 0)"

count_def
   "count M x == countm M (%y.y = x)"

induction
   "[| P({|}); !!M x. P(M) ==> P(addm M x) |] ==> P(M)"

end
