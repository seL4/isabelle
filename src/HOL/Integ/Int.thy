(*  Title:      Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

Int = IntDef +

instance int :: order (zle_refl,zle_trans,zle_anti_sym,int_less_le)
instance int :: plus_ac0 (zadd_commute,zadd_assoc,zadd_zero)
instance int :: linorder (zle_linear)

constdefs
  nat  :: int => nat
  "nat(Z) == if neg Z then 0 else (@ m. Z = int m)"

defs
  zabs_def  "abs(i::int) == if i < 0 then -i else i"

end
