(*  Title:      HOL/ex/Factorization.thy
    ID:         $Id$
    Author:     Thomas Marthedal Rasmussen
    Copyright   2000  University of Cambridge

Fundamental Theorem of Arithmetic (unique factorization into primes)
*)


Factorization = Primes + Perm +

consts
  primel  :: nat list => bool 
  nondec  :: nat list => bool 
  prod    :: nat list => nat
  oinsert :: [nat, nat list] => nat list
  sort    :: nat list => nat list

defs
  primel_def "primel xs == set xs <= prime"

primrec
  "nondec []     = True"
  "nondec (x#xs) = (case xs of [] => True | y#ys => x<=y & nondec xs)"

primrec
  "prod []     = 1"
  "prod (x#xs) = x * prod xs"

primrec
  "oinsert x []     = [x]"
  "oinsert x (y#ys) = (if x<=y then x#y#ys else y#oinsert x ys)"

primrec
  "sort []     = []"
  "sort (x#xs) = oinsert x (sort xs)"  

end