(*  Title: 	Terms.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Terms = Cube+

consts
  lambda	:: i
  unmark	:: i=>i
  Apl		:: [i,i]=>i

translations
  "Apl(n,m)" == "App(0,n,m)"
  
inductive
  domains       "lambda" <= "redexes"
  intrs
    Lambda_Var	"               n:nat ==>     Var(n):lambda"
    Lambda_Fun	"            u:lambda ==>     Fun(u):lambda"
    Lambda_App	"[|u:lambda; v:lambda|]==> Apl(u,v):lambda"
  type_intrs	"redexes.intrs@bool_typechecks"

defs
  unmark_def	"unmark(u) == redex_rec(u,%i.Var(i),   
		                          %x m.Fun(m),   
		                          %b x y m p.Apl(m,p))"
end


