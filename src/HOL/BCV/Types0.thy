(*  Title:      HOL/BCV/Types0.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Types for the register machine
*)

Types0 = SemiLattice +

datatype typ = Atyp | Btyp | Ctyp | Top

instance typ :: ord
instance typ :: plus

defs
le_typ "t1 <= t2 == (t1=t2) | (t1=Atyp & t2=Btyp) | (t2=Top)"
less_typ "(t1::typ) < t2 == t1 <= t2 & t1 ~= t2"
plus_typ "t1 + t2 == if t1<=t2 then t2 else if t2 <= t1 then t1 else Top"

end
