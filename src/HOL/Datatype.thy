(*  Title:      HOL/Datatype.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1998  TU Muenchen
*)

Datatype = Datatype_Universe +

rep_datatype bool
  distinct True_not_False, False_not_True
  induct   bool_induct

rep_datatype sum
  distinct Inl_not_Inr, Inr_not_Inl
  inject   Inl_eq, Inr_eq
  induct   sum_induct

rep_datatype prod
  inject   Pair_eq
  induct   prod_induct

rep_datatype unit
  induct   unit_induct

end
