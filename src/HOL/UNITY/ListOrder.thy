(*  Title:      HOL/UNITY/ListOrder
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Lists are partially ordered by the prefix relation
*)

ListOrder = GenPrefix +

instance list :: (term) order
    (prefix_refl,prefix_trans,prefix_antisym,prefix_less_le)

end
