(*  Title       : NSA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Infinite numbers, Infinitesimals,
                  infinitely close relation etc.
*) 

NSA = HRealAbs + RComplete +

constdefs

   (* standard real numbers reagarded as *)
   (* an embedded subset of hyperreals   *)
   SReal  :: "hypreal set"
   "SReal == {x. EX r. x = hypreal_of_real r}"

   Infinitesimal  :: "hypreal set"
   "Infinitesimal == {x. ALL r: SReal. 0 < r --> abs x < r}"

   HFinite :: "hypreal set"
   "HFinite == {x. EX r: SReal. abs x < r}"

   HInfinite :: "hypreal set"
   "HInfinite == {x. ALL r: SReal. r < abs x}"

consts   

    (* standard part map *)
    st       :: hypreal => hypreal

    (* infinitely close *)
    "@="     :: [hypreal,hypreal] => bool  (infixl 50)  

    monad    :: hypreal => hypreal set
    galaxy   :: hypreal => hypreal set

defs  

   inf_close_def  "x @= y       == (x + -y) : Infinitesimal"     
   st_def         "st           == (%x. @r. x : HFinite & r:SReal & r @= x)"

   monad_def      "monad x      == {y. x @= y}"
   galaxy_def     "galaxy x     == {y. (x + -y) : HFinite}"
 
end




