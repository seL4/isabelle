(*  Title:      HOL/Datatype.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1998  TU Muenchen
*)

Datatype = Univ +

rep_datatype sum
  distinct Inl_not_Inr, Inr_not_Inl
  inject   Inl_eq, Inr_eq
  induct   sum_induct

rep_datatype prod
  inject   Pair_eq
  induct   prod_induct

end
