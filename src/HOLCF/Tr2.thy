(*  Title: 	HOLCF/tr2.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduce infix if_then_else_fi and boolean connectives andalso, orelse
*)

Tr2 = Tr1 +

consts
	"@cifte"	:: "tr=>'c=>'c=>'c"
                             ("(3If _/ (then _/ else _) fi)" 60)
	"Icifte"        :: "tr->'c->'c->'c"

	"@andalso"	:: "tr => tr => tr" ("_ andalso _" [36,35] 35)
	"cop @andalso"	:: "tr -> tr -> tr" ("trand")
	"@orelse"	:: "tr => tr => tr" ("_ orelse _"  [31,30] 30)
	"cop @orelse"	:: "tr -> tr -> tr" ("tror")

        "neg"           :: "tr -> tr"

rules

  ifte_def    "Icifte == (LAM t e1 e2.tr_when[e1][e2][t])"
  andalso_def "trand == (LAM t1 t2.tr_when[t2][FF][t1])"
  orelse_def  "tror  == (LAM t1 t2.tr_when[TT][t2][t1])"
  neg_def     "neg == (LAM t. tr_when[FF][TT][t])"

end

ML

(* ----------------------------------------------------------------------*)
(* translations for the above mixfixes                                   *)
(* ----------------------------------------------------------------------*)

fun ciftetr ts =
	let val Cfapp = Const("fapp",dummyT) in	
	Cfapp $ 
	   	(Cfapp $
			(Cfapp$Const("Icifte",dummyT)$(nth_elem (0,ts)))$
		(nth_elem (1,ts)))$
	(nth_elem (2,ts))
	end;


val parse_translation = [("@andalso",mk_cinfixtr "@andalso"),
			("@orelse",mk_cinfixtr "@orelse"),
			("@cifte",ciftetr)];

val print_translation = [];





