(*  Title:      HOLCF/Up1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


Lifting

*)

Up1 = Cfun3 + Sum + 

(* new type for lifting *)

typedef (Up) ('a) "u" = "{x::(unit + 'a).True}"

instance u :: (sq_ord)sq_ord

consts
  Iup         :: "'a => ('a)u"
  Ifup        :: "('a->'b)=>('a)u => 'b"

defs
  Iup_def     "Iup x == Abs_Up(Inr(x))"
  Ifup_def    "Ifup(f)(x)== case Rep_Up(x) of Inl(y) => UU | Inr(z) => f`z"
  less_up_def "(op <<) == (%x1 x2. case Rep_Up(x1) of                 
               Inl(y1) => True          
             | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False       
                                            | Inr(z2) => y2<<z2))"
end
