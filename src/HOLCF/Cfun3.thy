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
strictify_def   "strictify == (LAM f x.Istrictify f x)"

end
