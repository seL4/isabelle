(*  Title:      HOL/Induct/MultisetOrder.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Multisets are partially ordered.
*)

theory MultisetOrder = Multiset:

instance multiset :: (order) order
  apply intro_classes
     apply (rule mult_le_refl)
    apply (erule mult_le_trans)
    apply assumption
   apply (erule mult_le_antisym)
   apply assumption
  apply (rule mult_less_le)
  done

instance multiset :: ("term") plus_ac0
  apply intro_classes
    apply (rule union_commute)
   apply (rule union_assoc)
  apply simp
  done

end
