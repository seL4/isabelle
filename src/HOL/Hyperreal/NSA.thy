(*  Title       : NSA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Infinite numbers, Infinitesimals,
                  infinitely close relation etc.
*) 

NSA = HRealAbs + RComplete +

constdefs

  Infinitesimal  :: "hypreal set"
   "Infinitesimal == {x. ALL r: Reals. 0 < r --> abs x < r}"

  HFinite :: "hypreal set"
   "HFinite == {x. EX r: Reals. abs x < r}"

  HInfinite :: "hypreal set"
   "HInfinite == {x. ALL r: Reals. r < abs x}"

  (* standard part map *)
  st        :: hypreal => hypreal
   "st           == (%x. @r. x : HFinite & r:Reals & r @= x)"

  monad     :: hypreal => hypreal set
   "monad x      == {y. x @= y}"

  galaxy    :: hypreal => hypreal set
   "galaxy x     == {y. (x + -y) : HFinite}"
 
  (* infinitely close *)
  approx :: "[hypreal, hypreal] => bool"    (infixl "@=" 50)
   "x @= y       == (x + -y) : Infinitesimal"     


defs  

   (*standard real numbers as a subset of the hyperreals*)
   SReal_def      "Reals == {x. EX r. x = hypreal_of_real r}"

syntax (symbols)
    approx :: "[hypreal, hypreal] => bool"    (infixl "\\<approx>" 50)
  
end




