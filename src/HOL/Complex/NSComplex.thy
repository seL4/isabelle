(*  Title:       NSComplex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Nonstandard Complex numbers
*)

NSComplex = NSInduct + 

constdefs
    hcomplexrel :: "((nat=>complex)*(nat=>complex)) set"
    "hcomplexrel == {p. EX X Y. p = ((X::nat=>complex),Y) & 
                        {n::nat. X(n) = Y(n)}: FreeUltrafilterNat}"

typedef hcomplex = "{x::nat=>complex. True}//hcomplexrel"      (quotient_def)

instance
   hcomplex  :: {zero,one,plus,times,minus,power,inverse}
  
defs
  hcomplex_zero_def 
  "0 == Abs_hcomplex(hcomplexrel `` {%n. (0::complex)})"
  
  hcomplex_one_def  
  "1 == Abs_hcomplex(hcomplexrel `` {%n. (1::complex)})"


  hcomplex_minus_def
  "- z == Abs_hcomplex(UN X: Rep_hcomplex(z). hcomplexrel `` {%n::nat. - (X n)})"

  hcomplex_diff_def
  "w - z == w + -(z::hcomplex)"
  
constdefs

  hcomplex_of_complex :: complex => hcomplex
  "hcomplex_of_complex z == Abs_hcomplex(hcomplexrel `` {%n. z})"
 
  hcinv  :: hcomplex => hcomplex
  "inverse(P)   == Abs_hcomplex(UN X: Rep_hcomplex(P). 
                    hcomplexrel `` {%n. inverse(X n)})"

  (*--- real and Imaginary parts ---*)
  
  hRe :: hcomplex => hypreal
  "hRe(z) == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. Re (X n)})"

  hIm :: hcomplex => hypreal
  "hIm(z) == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. Im (X n)})"   


  (*----------- modulus ------------*)

  hcmod :: hcomplex => hypreal
  "hcmod z == Abs_hypreal(UN X: Rep_hcomplex(z).
			  hyprel `` {%n. cmod (X n)})"

  (*------ imaginary unit ----------*)					 
			      
  iii :: hcomplex			      
  "iii == Abs_hcomplex(hcomplexrel `` {%n. ii})"

  (*------- complex conjugate ------*)

  hcnj :: hcomplex => hcomplex
  "hcnj z == Abs_hcomplex(UN X:Rep_hcomplex(z). hcomplexrel `` {%n. cnj (X n)})"

  (*------------ Argand -------------*)		       

  hsgn :: hcomplex => hcomplex
  "hsgn z == Abs_hcomplex(UN X:Rep_hcomplex(z). hcomplexrel `` {%n. sgn(X n)})"

  harg :: hcomplex => hypreal
  "harg z == Abs_hypreal(UN X:Rep_hcomplex(z). hyprel `` {%n. arg(X n)})"

  (* abbreviation for (cos a + i sin a) *)
  hcis :: hypreal => hcomplex
  "hcis a == Abs_hcomplex(UN X:Rep_hypreal(a). hcomplexrel `` {%n. cis (X n)})"

  (* abbreviation for r*(cos a + i sin a) *)
  hrcis :: [hypreal, hypreal] => hcomplex
  "hrcis r a == hcomplex_of_hypreal r * hcis a"

  (*----- injection from hyperreals -----*)			   
 
  hcomplex_of_hypreal :: hypreal => hcomplex
  "hcomplex_of_hypreal r == Abs_hcomplex(UN X:Rep_hypreal(r).
			       hcomplexrel `` {%n. complex_of_real (X n)})"

  (*------------ e ^ (x + iy) ------------*)

  hexpi :: hcomplex => hcomplex
  "hexpi z == hcomplex_of_hypreal(( *f* exp) (hRe z)) * hcis (hIm z)"
   

defs  


  (*----------- division ----------*)

  hcomplex_divide_def
  "w / (z::hcomplex) == w * inverse z"
    
  hcomplex_add_def
  "w + z == Abs_hcomplex(UN X:Rep_hcomplex(w). UN Y:Rep_hcomplex(z).
		      hcomplexrel `` {%n. X n + Y n})"

  hcomplex_mult_def
  "w * z == Abs_hcomplex(UN X:Rep_hcomplex(w). UN Y:Rep_hcomplex(z).
		      hcomplexrel `` {%n. X n * Y n})"    


primrec
     hcomplexpow_0   "z ^ 0       = 1"
     hcomplexpow_Suc "z ^ (Suc n) = (z::hcomplex) * (z ^ n)"


consts
  "hcpow"  :: [hcomplex,hypnat] => hcomplex     (infixr 80)

defs
  (* hypernatural powers of nonstandard complex numbers *)
  hcpow_def
  "(z::hcomplex) hcpow (n::hypnat) 
      == Abs_hcomplex(UN X:Rep_hcomplex(z). UN Y: Rep_hypnat(n).
             hcomplexrel `` {%n. (X n) ^ (Y n)})"

end
