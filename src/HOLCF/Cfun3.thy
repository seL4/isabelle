(*  Title:      HOLCF/Cfun3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  -> for class pcpo

*)

Cfun3 = Cfun2 +

instance "->" :: (cpo,cpo)cpo              (cpo_cfun)
instance "->" :: (cpo,pcpo)pcpo            (least_cfun)

default pcpo

consts  
        Istrictify   :: "('a->'b)=>'a=>'b"
        strictify    :: "('a->'b)->'a->'b"
defs

Istrictify_def  "Istrictify f x == if x=UU then UU else f`x"    
strictify_def   "strictify == (LAM f x. Istrictify f x)"

consts
        ID      :: "('a::cpo) -> 'a"
        cfcomp  :: "('b->'c)->(('a::cpo)->('b::cpo))->'a->('c::cpo)"

syntax  "@oo"   :: "('b->'c)=>('a->'b)=>'a->'c" ("_ oo _" [101,100] 100)
     
translations    "f1 oo f2" == "cfcomp`f1`f2"

defs

  ID_def        "ID ==(LAM x. x)"
  oo_def        "cfcomp == (LAM f g x. f`(g`x))" 

end
