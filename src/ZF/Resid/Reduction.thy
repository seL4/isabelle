(*  Title:      Reduction.thy
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Reduction = Terms+

consts
  Sred1, Sred,  Spar_red1,Spar_red    :: i
  "-1->","--->","=1=>",   "===>"      :: [i,i]=>o (infixl 50)

translations
  "a -1-> b" == "<a,b>:Sred1"
  "a ---> b" == "<a,b>:Sred"
  "a =1=> b" == "<a,b>:Spar_red1"
  "a ===> b" == "<a,b>:Spar_red"
  
  
inductive
  domains       "Sred1" <= "lambda*lambda"
  intrs
    beta        "[|m \\<in> lambda; n \\<in> lambda|] ==> Apl(Fun(m),n) -1-> n/m"
    rfun        "[|m -1-> n|] ==> Fun(m) -1-> Fun(n)"
    apl_l       "[|m2 \\<in> lambda; m1 -1-> n1|] ==>   
                                  Apl(m1,m2) -1-> Apl(n1,m2)"
    apl_r       "[|m1 \\<in> lambda; m2 -1-> n2|] ==>   
                                  Apl(m1,m2) -1-> Apl(m1,n2)"
  type_intrs    "red_typechecks"

inductive
  domains       "Sred" <= "lambda*lambda"
  intrs
    one_step    "[|m-1->n|] ==> m--->n"
    refl        "m \\<in> lambda==>m --->m"
    trans       "[|m--->n; n--->p|]==>m--->p"
  type_intrs    "[Sred1.dom_subset RS subsetD]@red_typechecks"

inductive
  domains       "Spar_red1" <= "lambda*lambda"
  intrs
    beta        "[|m =1=> m';   
                 n =1=> n'|] ==> Apl(Fun(m),n) =1=> n'/m'"
    rvar        "n \\<in> nat==> Var(n) =1=> Var(n)"
    rfun        "[|m =1=> m'|]==> Fun(m) =1=> Fun(m')"
    rapl        "[|m =1=> m';   
                 n =1=> n'|] ==> Apl(m,n) =1=> Apl(m',n')"
  type_intrs    "red_typechecks"

  inductive
  domains       "Spar_red" <= "lambda*lambda"
  intrs
    one_step    "[|m =1=> n|] ==> m ===> n"
    trans       "[|m===>n; n===>p|]==>m===>p"
  type_intrs    "[Spar_red1.dom_subset RS subsetD]@red_typechecks"


end

