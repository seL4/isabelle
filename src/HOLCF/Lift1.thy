Lift1 = Tr2 + 

default term

datatype 'a lift  = Undef | Def('a)

arities "lift" :: (term)term

consts less_lift    :: "['a lift, 'a lift] => bool"
       UU_lift      :: "'a lift"

defs 
 
 less_lift_def  "less_lift x y == (x=y | x=Undef)"


end

