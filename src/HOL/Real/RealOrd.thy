(*  Title:	 Real/RealOrd.thy
    ID: 	 $Id$
    Author:      Jacques D. Fleuriot and Lawrence C. Paulson
    Copyright:   1998  University of Cambridge
    Description: Type "real" is a linear order and also 
                 satisfies plus_ac0: + is an AC-operator with zero
*)

RealOrd = RealDef +

instance real :: order (real_le_refl,real_le_trans,real_le_anti_sym,real_less_le)
instance real :: linorder (real_le_linear)

instance real :: plus_ac0 (real_add_commute,real_add_assoc,real_add_zero_left)

end
