(*  Title:      HOLCF/cprod3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Class instance of  * for class pcpo

*)

Cprod3 = Cprod2 +

arities "*" :: (pcpo,pcpo)pcpo                  (* Witness cprod2.ML *)

consts  
        cpair        :: "'a -> 'b -> ('a*'b)" (* continuous  pairing *)
        cfst         :: "('a*'b)->'a"
        csnd         :: "('a*'b)->'b"
        csplit       :: "('a->'b->'c)->('a*'b)->'c"

syntax  
        "@ctuple"    :: "['a, args] => 'a * 'b"         ("(1<_,/ _>)")


translations 
        "<x, y, z>"   == "<x, <y, z>>"
        "<x, y>"      == "cpair`x`y"

rules 

inst_cprod_pcpo "(UU::'a*'b) = (UU,UU)"

defs
cpair_def       "cpair  == (LAM x y.(x,y))"
cfst_def        "cfst   == (LAM p.fst(p))"
csnd_def        "csnd   == (LAM p.snd(p))"      
csplit_def      "csplit == (LAM f p.f`(cfst`p)`(csnd`p))"



(* introduce syntax for

   Let <x,y> = e1; z = E2 in E3

   and

   ¤<x,y,z>.e
*)

types
  Cletbinds  Cletbind 

consts
  CLet           :: "'a -> ('a -> 'b) -> 'b"

syntax
  (* syntax for Let *) 

  "_Cbind"  :: "[pttrn, 'a] => Cletbind"             ("(2_ =/ _)" 10)
  ""        :: "Cletbind => Cletbinds"               ("_")
  "_Cbinds" :: "[Cletbind, Cletbinds] => Cletbinds"  ("_;/ _")
  "_CLet"   :: "[Cletbinds, 'a] => 'a"                ("(Let (_)/ in (_))" 10)

translations
  (* translation for Let *)
  "_CLet (_Cbinds b bs) e"  == "_CLet b (_CLet bs e)"
  "Let x = a in e"          == "CLet`a`(LAM x.e)"

defs
  (* Misc Definitions *)
  CLet_def       "CLet == LAM s. LAM f.f`s"


syntax
  (* syntax for LAM <x,y,z>.E *)
  "@Cpttrn"  :: "[pttrn,pttrns] => pttrn"              ("<_,/_>")

translations
  (* translations for LAM <x,y,z>.E *)
  "LAM <x,y,zs>.b"   == "csplit`(LAM x.LAM <y,zs>.b)"
  "LAM <x,y>.b"      == "csplit`(LAM x.LAM y.b)"
  (* reverse translation <= does not work yet !! *)

(* start 8bit 1 *)
translations
  "Let x = a in e"          == "CLet`a`(¤ x.e)"

(* end 8bit 1 *)
end




