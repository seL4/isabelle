(*  Title: 	Conversion.thy
    ID:         $Id$
    Author: 	Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF

*)

Conversion = Confluence+

consts
  Sconv1	:: i
  "<-1->"	:: [i,i]=>o (infixl 50)
  Sconv		:: i
  "<--->"	:: [i,i]=>o (infixl 50)

translations
  "a<-1->b"    == "<a,b>:Sconv1"
  "a<--->b"    == "<a,b>:Sconv"
  
inductive
  domains       "Sconv1" <= "lambda*lambda"
  intrs
    red1	"m -1-> n ==> m<-1->n"
    expl  	"n -1-> m ==> m<-1->n"
  type_intrs	"[red1D1,red1D2]@lambda.intrs@bool_typechecks"

inductive
  domains       "Sconv" <= "lambda*lambda"
  intrs
    one_step	"m<-1->n  ==> m<--->n"
    refl  	"m:lambda ==> m<--->m"
    trans	"[|m<--->n; n<--->p|] ==> m<--->p"
  type_intrs	"[Sconv1.dom_subset RS subsetD]@lambda.intrs@bool_typechecks"
end

