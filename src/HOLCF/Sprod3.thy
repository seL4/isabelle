(*  Title:      HOLCF/sprod3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ** for class pcpo
*)

Sprod3 = Sprod2 +

arities "**" :: (pcpo,pcpo)pcpo                 (* Witness sprod2.ML *)

consts  
  spair		:: "'a -> 'b -> ('a**'b)" (* continuous strict pairing *)
  sfst		:: "('a**'b)->'a"
  ssnd		:: "('a**'b)->'b"
  ssplit	:: "('a->'b->'c)->('a**'b)->'c"

syntax  
  "@stuple"	:: "['a, args] => 'a ** 'b"		("(1'(|_,/ _|'))")

translations
        "(|x, y, z|)"   == "(|x, (|y, z|)|)"
        "(|x, y|)"      == "spair`x`y"

syntax (symbols)
  "@stuple"	:: "['a, args] => 'a ** 'b"		("(1\\<lparr>_,/ _\\<rparr>)")

rules 

inst_sprod_pcpo "(UU::'a**'b) = Ispair UU UU"

defs
spair_def       "spair  == (LAM x y.Ispair x y)"
sfst_def        "sfst   == (LAM p.Isfst p)"
ssnd_def        "ssnd   == (LAM p.Issnd p)"     
ssplit_def      "ssplit == (LAM f. strictify`(LAM p.f`(sfst`p)`(ssnd`p)))"


end



