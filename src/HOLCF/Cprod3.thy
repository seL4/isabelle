(*  Title:      HOLCF/Cprod3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of * for class pcpo and cpo.
*)

Cprod3 = Cprod2 +

instance "*" :: (cpo,cpo)cpo   	  (cpo_cprod)
instance "*" :: (pcpo,pcpo)pcpo   (least_cprod)

consts
        cpair        :: "'a -> 'b -> ('a*'b)" (* continuous pairing *)
        cfst         :: "('a*'b)->'a"
        csnd         :: "('a*'b)->'b"
        csplit       :: "('a->'b->'c)->('a*'b)->'c"

syntax
        "@ctuple"    :: "['a, args] => 'a * 'b"         ("(1<_,/ _>)")

translations
        "<x, y, z>"   == "<x, <y, z>>"
        "<x, y>"      == "cpair$x$y"

defs
cpair_def       "cpair  == (LAM x y.(x,y))"
cfst_def        "cfst   == (LAM p. fst(p))"
csnd_def        "csnd   == (LAM p. snd(p))"      
csplit_def      "csplit == (LAM f p. f$(cfst$p)$(csnd$p))"



(* introduce syntax for

   Let <x,y> = e1; z = E2 in E3

   and

   LAM <x,y,z>.e
*)

constdefs
  CLet           :: "'a -> ('a -> 'b) -> 'b"
  "CLet == LAM s f. f$s"


(* syntax for Let *)

types
  Cletbinds  Cletbind

syntax
  "_Cbind"  :: "[pttrn, 'a] => Cletbind"             ("(2_ =/ _)" 10)
  ""        :: "Cletbind => Cletbinds"               ("_")
  "_Cbinds" :: "[Cletbind, Cletbinds] => Cletbinds"  ("_;/ _")
  "_CLet"   :: "[Cletbinds, 'a] => 'a"               ("(Let (_)/ in (_))" 10)

translations
  "_CLet (_Cbinds b bs) e"  == "_CLet b (_CLet bs e)"
  "Let x = a in e"          == "CLet$a$(LAM x. e)"


(* syntax for LAM <x,y,z>.e *)

syntax
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3LAM <_>./ _)" [0, 10] 10)

translations
  "LAM <x,y,zs>.b"        == "csplit$(LAM x. LAM <y,zs>.b)"
  "LAM <x,y>. LAM zs. b"  <= "csplit$(LAM x y zs. b)"
  "LAM <x,y>.b"           == "csplit$(LAM x y. b)"

syntax (symbols)
  "_LAM"    :: "[patterns, 'a => 'b] => ('a -> 'b)"  ("(3\\<Lambda>()<_>./ _)" [0, 10] 10)

end
