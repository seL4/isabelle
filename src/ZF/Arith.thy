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
    raw_add, raw_diff, raw_mult  :: [i,i]=>i

primrec
  "raw_add (0, n) = n"
  "raw_add (succ(m), n) = succ(raw_add(m, n))"

primrec
  raw_diff_0     "raw_diff(m, 0) = m"
  raw_diff_succ  "raw_diff(m, succ(n)) = 
                    nat_case(0, %x. x, raw_diff(m, n))"

primrec
  "raw_mult(0, n) = 0"
  "raw_mult(succ(m), n) = raw_add (n, raw_mult(m, n))"
 
constdefs
  add :: [i,i]=>i                    (infixl "#+" 65)
    "m #+ n == raw_add (natify(m), natify(n))"

  diff :: [i,i]=>i                    (infixl "#-" 65)
    "m #- n == raw_diff (natify(m), natify(n))"

  mult :: [i,i]=>i                    (infixl "#*" 70)
    "m #* n == raw_mult (natify(m), natify(n))"

  raw_div  :: [i,i]=>i
    "raw_div (m, n) == 
       transrec(m, %j f. if j<n | n=0 then 0 else succ(f`(j#-n)))"

  raw_mod  :: [i,i]=>i
    "raw_mod (m, n) == 
       transrec(m, %j f. if j<n | n=0 then j else f`(j#-n))"

  div  :: [i,i]=>i                    (infixl "div" 70) 
    "m div n == raw_div (natify(m), natify(n))"

  mod  :: [i,i]=>i                    (infixl "mod" 70)
    "m mod n == raw_mod (natify(m), natify(n))"

end
