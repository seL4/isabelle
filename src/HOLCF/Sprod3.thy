(*  Title:      HOLCF/sprod3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ** for class pcpo
*)

Sprod3 = Sprod2 +

instance "**" :: (pcpo,pcpo)pcpo  (least_sprod,cpo_sprod)

consts  
  spair		:: "'a -> 'b -> ('a**'b)" (* continuous strict pairing *)
  sfst		:: "('a**'b)->'a"
  ssnd		:: "('a**'b)->'b"
  ssplit	:: "('a->'b->'c)->('a**'b)->'c"

syntax  
  "@stuple"	:: "['a, args] => 'a ** 'b"	("(1'(:_,/ _:'))")

translations
        "(:x, y, z:)"   == "(:x, (:y, z:):)"
        "(:x, y:)"      == "spair$x$y"

defs
spair_def       "spair  == (LAM x y. Ispair x y)"
sfst_def        "sfst   == (LAM p. Isfst p)"
ssnd_def        "ssnd   == (LAM p. Issnd p)"     
ssplit_def      "ssplit == (LAM f. strictify$(LAM p. f$(sfst$p)$(ssnd$p)))"

end
