(*  Title:      HOLCF/Tr.thy
    ID:         $Id$
    Author:     Franz Regensburger

Introduce infix if_then_else_fi and boolean connectives andalso, orelse
*)

Tr = Lift + Fix +

types
  tr = "bool lift"

translations
  "tr" <= (type) "bool lift" 

consts
	TT,FF           :: "tr"
        Icifte          :: "tr -> 'c -> 'c -> 'c"
        trand           :: "tr -> tr -> tr"
        tror            :: "tr -> tr -> tr"
        neg             :: "tr -> tr"
        If2             :: "tr=>'c=>'c=>'c"

syntax  "@cifte"        :: "tr=>'c=>'c=>'c" ("(3If _/ (then _/ else _) fi)" 60)
        "@andalso"      :: "tr => tr => tr" ("_ andalso _" [36,35] 35)
        "@orelse"       :: "tr => tr => tr" ("_ orelse _"  [31,30] 30)
 
translations 
	     "x andalso y" == "trand$x$y"
             "x orelse y"  == "tror$x$y"
             "If b then e1 else e2 fi" == "Icifte$b$e1$e2"
defs
  TT_def      "TT==Def True"
  FF_def      "FF==Def False"
  neg_def     "neg == flift2 Not"
  ifte_def    "Icifte == (LAM b t e. flift1(%b. if b then t else e)$b)"
  andalso_def "trand == (LAM x y. If x then y else FF fi)"
  orelse_def  "tror == (LAM x y. If x then TT else y fi)"
  If2_def     "If2 Q x y == If Q then x else y fi"

end

