(*  Title:      ZF/arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Arithmetic operators and their definitions
*)

Arith = Epsilon + 

setup setup_datatypes

(*The natural numbers as a datatype*)
rep_datatype 
  elim		natE
  induct	nat_induct
  case_eqns	nat_case_0, nat_case_succ
  recursor_eqns recursor_0, recursor_succ


consts
    "#*" :: [i,i]=>i                    (infixl 70)
    div  :: [i,i]=>i                    (infixl 70) 
    mod  :: [i,i]=>i                    (infixl 70)
    "#+" :: [i,i]=>i                    (infixl 65)
    "#-" :: [i,i]=>i                    (infixl 65)

primrec
  add_0     "0 #+ n = n"
  add_succ  "succ(m) #+ n = succ(m #+ n)"

primrec
  diff_0     "m #- 0 = m"
  diff_SUCC  "m #- succ(n) = nat_case(0, %x. x, m #- n)"

primrec
  mult_0    "0 #* n = 0"
  mult_succ "succ(m) #* n = n #+ (m #* n)"
 
defs
    mod_def  "m mod n == transrec(m, %j f. if j<n then j else f`(j#-n))"
    div_def  "m div n == transrec(m, %j f. if j<n then 0 else succ(f`(j#-n)))"
end
