(*  Title:	 Real/Hyperreal/HyperOrd.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh
    Description: Type "hypreal" is a linear order and also 
                 satisfies plus_ac0: + is an AC-operator with zero
*)

HyperOrd = HyperDef +

instance hypreal :: order (hypreal_le_refl,hypreal_le_trans,hypreal_le_anti_sym,hypreal_less_le)
instance hypreal :: linorder (hypreal_le_linear)

instance hypreal :: plus_ac0(hypreal_add_commute,hypreal_add_assoc,hypreal_add_zero_left)

end
