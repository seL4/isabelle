(*  Title:       Real/Real.thy
    Author:      Lawrence C. Paulson
                 Jacques D. Fleuriot
    Copyright:   1998  University of Cambridge
    Description: Type "real" is a linear order
*)

Real = RealDef +

instance real :: order (real_le_refl,real_le_trans,real_le_anti_sym,real_less_le)
instance real :: linorder (real_le_linear)

end
