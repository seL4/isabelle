(*  Title:      HOL/BCV/Types.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

Types for the register machine
*)

Types = Types0 +

instance typ :: order (le_typ_refl,le_typ_trans,le_typ_antisym,less_le_typ)

end
