(*  Title:      Real/Real.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "real" is a linear order
*)

Real = RealDef +

instance real :: order (real_le_refl,real_le_trans,real_le_anti_sym,real_less_le)
instance real :: linorder (real_le_linear)

end
