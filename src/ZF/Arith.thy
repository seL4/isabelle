(*  Title:      ZF/arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Arithmetic operators and their definitions
*)

Arith = Univ + 

constdefs
  pred   :: i=>i    (*inverse of succ*)
    "pred(y) == THE x. y = succ(x)"

  natify :: i=>i    (*coerces non-nats to nats*)
    "natify == Vrecursor(%f a. if a = succ(pred(a)) then succ(f`pred(a))
                                                    else 0)"

consts
    "##*" :: [i,i]=>i                    (infixl 70)
    "##+" :: [i,i]=>i                    (infixl 65)
    "##-" :: [i,i]=>i                    (infixl 65)

primrec
  raw_add_0     "0 ##+ n = n"
  raw_add_succ  "succ(m) ##+ n = succ(m ##+ n)"

primrec
  raw_diff_0     "m ##- 0 = m"
  raw_diff_succ  "m ##- succ(n) = nat_case(0, %x. x, m ##- n)"

primrec
  raw_mult_0    "0 ##* n = 0"
  raw_mult_succ "succ(m) ##* n = n ##+ (m ##* n)"
 
constdefs
  add :: [i,i]=>i                    (infixl "#+" 65)
    "m #+ n == natify(m) ##+ natify(n)"

  diff :: [i,i]=>i                    (infixl "#-" 65)
    "m #- n == natify(m) ##- natify(n)"

  mult :: [i,i]=>i                    (infixl "#*" 70)
    "m #* n == natify(m) ##* natify(n)"

  div  :: [i,i]=>i                    (infixl "div" 70) 
    "m div n == transrec(m, %j f. if j<n then 0 else succ(f`(j#-n)))"

  mod  :: [i,i]=>i                    (infixl "mod" 70)
    "m mod n == transrec(m, %j f. if j<n then j else f`(j#-n))"

end
