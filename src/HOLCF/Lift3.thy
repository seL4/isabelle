(*  Title:      HOLCF/Lift3.thy
    ID:         $Id$
    Author:     Olaf Mueller, Robert Sandner
    Copyright   1996 Technische Universitaet Muenchen

Class Instance lift::(term)pcpo
*)

Lift3 = Lift2 + 

instance lift :: (term)pcpo (cpo_lift,least_lift)

consts 
 flift1      :: "('a => 'b::pcpo) => ('a lift -> 'b)"
 flift2      :: "('a => 'b) => ('a lift -> 'b lift)"

translations
 "UU" <= "Undef"

defs
 flift1_def
  "flift1 f  == (LAM x. (case x of 
                   Undef => UU
                 | Def y => (f y)))"
 flift2_def
  "flift2 f == (LAM x. (case x of 
                              Undef => Undef
                            | Def y => Def (f y)))"

end

