(*  Title       : CSeries.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2002  University of Edinburgh
    Description : Finite summation and infinite series for complex numbers
*)

CSeries = CStar +

consts sumc :: "[nat,nat,(nat=>complex)] => complex"
primrec
   sumc_0   "sumc m 0 f = 0"
   sumc_Suc "sumc m (Suc n) f = (if n < m then 0 else sumc m n f + f(n))"

(*  
constdefs

   needs convergence of complex sequences  

  csums  :: [nat=>complex,complex] => bool     (infixr 80)
   "f sums s  == (%n. sumr 0 n f) ----C> s"
  
   csummable :: (nat=>complex) => bool
   "csummable f == (EX s. f csums s)"

   csuminf   :: (nat=>complex) => complex
   "csuminf f == (@s. f csums s)"
*)

end

