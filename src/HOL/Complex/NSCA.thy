(*  Title       : NSCA.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001,2002 University of Edinburgh
    Description : Infinite, infinitesimal complex number etc! 
*)

NSCA = NSComplexArith + 

consts   

    (* infinitely close *)
    "@c="     :: [hcomplex,hcomplex] => bool  (infixl 50)  

  
constdefs
   (* standard complex numbers reagarded as an embedded subset of NS complex *)
   SComplex  :: "hcomplex set"
   "SComplex == {x. EX r. x = hcomplex_of_complex r}"

   CInfinitesimal  :: "hcomplex set"
   "CInfinitesimal == {x. ALL r: Reals. 0 < r --> hcmod x < r}"

   CFinite :: "hcomplex set"
   "CFinite == {x. EX r: Reals. hcmod x < r}"

   CInfinite :: "hcomplex set"
   "CInfinite == {x. ALL r: Reals. r < hcmod x}"

   (* standard part map *)  
   stc :: hcomplex => hcomplex
   "stc x == (@r. x : CFinite & r:SComplex & r @c= x)"

   cmonad    :: hcomplex => hcomplex set
   "cmonad x  == {y. x @c= y}"

   cgalaxy   :: hcomplex => hcomplex set
   "cgalaxy x == {y. (x - y) : CFinite}"


defs  

   capprox_def  "x @c= y == (x - y) : CInfinitesimal"     
 
end
