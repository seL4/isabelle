(*  Title: 	HOLCF/cfun3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  -> for class pcpo

*)

Cfun3 = Cfun2 +

arities "->"	:: (pcpo,pcpo)pcpo		(* Witness cfun2.ML *)

consts  
	Istrictify   :: "('a->'b)=>'a=>'b"
	strictify    :: "('a->'b)->'a->'b"

rules 

inst_cfun_pcpo	"(UU::'a->'b) = UU_cfun"

defs

Istrictify_def	"Istrictify f x == if x=UU then UU else f`x"	

strictify_def	"strictify == (LAM f x.Istrictify f x)"

end

