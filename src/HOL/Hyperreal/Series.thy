(*  Title       : Series.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Finite summation and infinite series
*) 


Series = SEQ + Lim +

consts sumr :: "[nat,nat,(nat=>real)] => real"
primrec
   sumr_0   "sumr m 0 f = 0"
   sumr_Suc "sumr m (Suc n) f = (if n < m then 0 
                               else sumr m n f + f(n))"

constdefs
   sums  :: [nat=>real,real] => bool     (infixr 80)
   "f sums s  == (%n. sumr 0 n f) ----> s"

   summable :: (nat=>real) => bool
   "summable f == (EX s. f sums s)"

   suminf   :: (nat=>real) => real
   "suminf f == (@s. f sums s)"
end


