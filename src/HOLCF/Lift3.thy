(*  Title:      HOLCF/Lift3.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996 Technische Universitaet Muenchen

Class Instance lift::(term)pcpo
*)

Lift3 = Lift2 + 

instance lift :: (term)pcpo (cpo_lift,least_lift)

consts 
 flift1      :: "('a => 'b::pcpo) => ('a lift -> 'b)"
 flift2      :: "('a => 'b)       => ('a lift -> 'b lift)"

 liftpair    ::"'a::term lift * 'b::term lift => ('a * 'b) lift"

translations
 "UU" <= "Undef"

defs
 flift1_def
  "flift1 f == (LAM x. (case x of 
                   Undef => UU
                 | Def y => (f y)))"
 flift2_def
  "flift2 f == (LAM x. (case x of 
                   Undef => UU
                 | Def y => Def (f y)))"
 liftpair_def
  "liftpair x  == (case (cfst$x) of 
                  Undef  => UU
                | Def x1 => (case (csnd$x) of 
                               Undef => UU
                             | Def x2 => Def (x1,x2)))"

end

