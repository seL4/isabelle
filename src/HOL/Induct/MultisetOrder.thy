(*  Title:      HOL/UNITY/MultisetOrder
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Multisets are partially ordered
*)

MultisetOrder = Multiset +

instance multiset :: (order) order
    (mult_le_refl,mult_le_trans,mult_le_antisym,mult_less_le)

end
