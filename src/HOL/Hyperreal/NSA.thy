(*  Title       : NSA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Infinite numbers, Infinitesimals,
                  infinitely close relation etc.
*) 

NSA = HRealAbs + RComplete +

constdefs

  Infinitesimal  :: "hypreal set"
   "Infinitesimal == {x. ALL r: SReal. 0 < r --> abs x < r}"

  HFinite :: "hypreal set"
   "HFinite == {x. EX r: SReal. abs x < r}"

  HInfinite :: "hypreal set"
   "HInfinite == {x. ALL r: SReal. r < abs x}"

  (* standard part map *)
  st        :: hypreal => hypreal
   "st           == (%x. @r. x : HFinite & r:SReal & r @= x)"

  monad     :: hypreal => hypreal set
   "monad x      == {y. x @= y}"

  galaxy    :: hypreal => hypreal set
   "galaxy x     == {y. (x + -y) : HFinite}"
 
  (* infinitely close *)
  inf_close :: "[hypreal, hypreal] => bool"    (infixl "@=" 50)
   "x @= y       == (x + -y) : Infinitesimal"     


defs  

   (*standard real numbers as a subset of the hyperreals*)
   SReal_def      "SReal == {x. EX r. x = hypreal_of_real r}"

syntax (symbols)
    inf_close :: "[hypreal, hypreal] => bool"    (infixl "\\<approx>" 50)
  
end




