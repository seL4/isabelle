(*  Title:      HOLCF/Up1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


Lifting

*)

Up1 = Cfun3 + Sum + 

(* new type for lifting *)

types "u" 1

arities "u" :: (pcpo)term       

consts

  Rep_Up      :: "('a)u => (void + 'a)"
  Abs_Up      :: "(void + 'a) => ('a)u"

  Iup         :: "'a => ('a)u"
  UU_up       :: "('a)u"
  Ifup        :: "('a->'b)=>('a)u => 'b"
  less_up     :: "('a)u => ('a)u => bool"

rules

  (*faking a type definition... *)
  (* ('a)u is isomorphic to void + 'a  *)

  Rep_Up_inverse  "Abs_Up(Rep_Up(p)) = p"     
  Abs_Up_inverse  "Rep_Up(Abs_Up(p)) = p"

   (*defining the abstract constants*)

defs

  UU_up_def   "UU_up == Abs_Up(Inl(UU))"
  Iup_def     "Iup x == Abs_Up(Inr(x))"

  Ifup_def    "Ifup(f)(x)== case Rep_Up(x) of Inl(y) => UU | Inr(z) => f`z"
 
  less_up_def "less_up(x1)(x2) == (case Rep_Up(x1) of                 
               Inl(y1) => True          
             | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False       
                                            | Inr(z2) => y2<<z2))"

end
