(*  Title       : HSeries.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Finite summation and infinite series
                  for hyperreals
*) 

HSeries = Series +

consts 
   sumhr :: "(hypnat * hypnat * (nat=>real)) => hypreal"

defs
   sumhr_def
   "sumhr p
       == Abs_hypreal(UN X:Rep_hypnat(fst p). 
              UN Y: Rep_hypnat(fst(snd p)).
              hyprel```{%n::nat. sumr (X n) (Y n) (snd(snd p))})"

constdefs
   NSsums  :: [nat=>real,real] => bool     (infixr 80)
   "f NSsums s  == (%n. sumr 0 n f) ----NS> s"

   NSsummable :: (nat=>real) => bool
   "NSsummable f == (EX s. f NSsums s)"

   NSsuminf   :: (nat=>real) => real
   "NSsuminf f == (@s. f NSsums s)"

end
