(*  Title:      HOLCF/Lift1.thy
    ID:         $Id$
    Author:     Olaf Mueller, Robert Sandner
    Copyright   1996 Technische Universitaet Muenchen

Lifting types of class term to flat pcpo's
*)

Lift1 = Tr2 + 

default term

datatype 'a lift  = Undef | Def('a)

arities "lift" :: (term)term

consts less_lift    :: "['a lift, 'a lift] => bool"
       UU_lift      :: "'a lift"

defs 
 
 less_lift_def  "less_lift x y == (x=y | x=Undef)"


end

