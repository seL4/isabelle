(*  Title: 	HOLCF/tr2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduce infix if_then_else_fi and boolean connectives andalso, orelse
*)

Tr2 = Tr1 +

consts
	Icifte		:: "tr -> 'c -> 'c -> 'c"
	trand		:: "tr -> tr -> tr"
	tror		:: "tr -> tr -> tr"
        neg		:: "tr -> tr"

syntax 	"@cifte"	:: "tr=>'c=>'c=>'c"
                             ("(3If _/ (then _/ else _) fi)" 60)
	"@andalso"	:: "tr => tr => tr" ("_ andalso _" [36,35] 35)
	"@orelse"	:: "tr => tr => tr" ("_ orelse _"  [31,30] 30)
 
translations "x andalso y" == "trand`x`y"
             "x orelse y"  == "tror`x`y"
             "If b then e1 else e2 fi" == "Icifte`b`e1`e2"
              
defs

  ifte_def    "Icifte == (LAM t e1 e2.tr_when`e1`e2`t)"
  andalso_def "trand == (LAM t1 t2.tr_when`t2`FF`t1)"
  orelse_def  "tror  == (LAM t1 t2.tr_when`TT`t2`t1)"
  neg_def     "neg == (LAM t. tr_when`FF`TT`t)"

end
