(*  Title: 	HOLCF/cinfix.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Some functions for the print and parse translation of continuous functions

Suppose the user introduces the following notation for the continuous
infixl . and the cont. infixr # with binding power 100

consts  
	"."     :: "'a => 'b => ('a**'b)" ("_._" [100,101] 100)
	"cop ." :: "'a -> 'b -> ('a**'b)" ("spair")

	"#"     :: "'a => 'b => ('a**'b)" ("_#_" [101,100] 100)
	"cop #" :: "'a -> 'b -> ('a**'b)" ("spair2")

the following functions are needed to set up proper translations
*)

(* -----------------------------------------------------------------------  
   a general purpose parse translation for continuous infix operators 
   this functions must be used for every cont. infix         
   ----------------------------------------------------------------------- *) 

fun mk_cinfixtr id =
	(fn ts =>
	let val Cfapp = Const("fapp",dummyT) in	
	Cfapp $ (Cfapp$Const("cop "^id,dummyT)$(nth_elem (0,ts)))$
	(nth_elem (1,ts))
	end);



(* -----------------------------------------------------------------------  
   make a print translation for a cont. infix operator "cop ???"    
   this is a print translation for fapp and is installed only once  
   special translations for other mixfixes (e.g. If_then_else_fi) are also 
   defined.
   ----------------------------------------------------------------------- *) 

fun fapptr' ts =
  case ts of
   [Const("fapp",T1)$Const(s,T2)$t1,t2] =>
	if ["c","o","p"," "] = take(4, explode s)
	  then Const(implode(drop(4, explode s)),dummyT)$t1$t2
	else raise Match
  | [Const("fapp",dummyT)$
	(Const("fapp",T1)$Const("Icifte",T2)$t)$e1,e2] 
      => Const("@cifte",dummyT)$t$e1$e2 
  | _ => raise Match;


(* -----------------------------------------------------------------------  

for the example above, the following must be setup in the ML section 

val parse_translation = [(".",mk_cinfixtr "."),
			 ("#",mk_cinfixtr "#")];


the print translation for fapp is setup only once in the system

val print_translation = [("fapp",fapptr')];

  ----------------------------------------------------------------------- *) 






