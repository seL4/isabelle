(*  Title:      Integ.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Type "int" is a linear order
*)

Integ = IntDef +

instance int :: order (zle_refl,zle_trans,zle_anti_sym,int_less_le)
instance int :: linorder (zle_linear)

constdefs
  zmagnitude  :: int => nat
  "zmagnitude(Z) == @m. Z = $# m | -Z = $# m"

end
