(*  Title:       Complex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Description: Complex numbers
*)

Complex = HLog + 

typedef complex = "{p::(real*real). True}"

instance
  complex :: {ord,zero,one,plus,minus,times,power,inverse}

consts
  "ii"    :: complex        ("ii") 

constdefs

  (*--- real and Imaginary parts ---*)
  
  Re :: complex => real
  "Re(z) == fst(Rep_complex z)"

  Im :: complex => real
  "Im(z) == snd(Rep_complex z)"

  (*----------- modulus ------------*)

  cmod :: complex => real
  "cmod z == sqrt(Re(z) ^ 2 + Im(z) ^ 2)"			      

  (*----- injection from reals -----*)			   
 
  complex_of_real :: real => complex
  "complex_of_real r == Abs_complex(r,0::real)"
				    
  (*------- complex conjugate ------*)

  cnj :: complex => complex
  "cnj z == Abs_complex(Re z, -Im z)"

  (*------------ Argand -------------*)		       

  sgn :: complex => complex
  "sgn z == z / complex_of_real(cmod z)"

  arg :: complex => real
  "arg z == @a. Re(sgn z) = cos a & Im(sgn z) = sin a & -pi < a & a <= pi"
									  
defs

  complex_zero_def
  "0 == Abs_complex(0::real,0)"

  complex_one_def
  "1 == Abs_complex(1,0::real)"

  (*------ imaginary unit ----------*)					 
			      
  i_def 
  "ii == Abs_complex(0::real,1)"

  (*----------- negation -----------*)
				     
  complex_minus_def
  "- (z::complex) == Abs_complex(-Re z, -Im z)"				     

  
  (*----------- inverse -----------*)
  complex_inverse_def
  "inverse (z::complex) == Abs_complex(Re(z)/(Re(z) ^ 2 + Im(z) ^ 2),
                            -Im(z)/(Re(z) ^ 2 + Im(z) ^ 2))"

  complex_add_def
  "w + (z::complex) == Abs_complex(Re(w) + Re(z),Im(w) + Im(z))"

  complex_diff_def
  "w - (z::complex) == w + -(z::complex)"

  complex_mult_def
  "w * (z::complex) == Abs_complex(Re(w) * Re(z) - Im(w) * Im(z),
			Re(w) * Im(z) + Im(w) * Re(z))"


  (*----------- division ----------*)
  complex_divide_def
  "w / (z::complex) == w * inverse z"
  

primrec
     complexpow_0   "z ^ 0       = complex_of_real 1"
     complexpow_Suc "z ^ (Suc n) = (z::complex) * (z ^ n)"


constdefs

  (* abbreviation for (cos a + i sin a) *)
  cis :: real => complex
  "cis a == complex_of_real(cos a) + ii * complex_of_real(sin a)"

  (* abbreviation for r*(cos a + i sin a) *)
  rcis :: [real, real] => complex
  "rcis r a == complex_of_real r * cis a"

  (* e ^ (x + iy) *)
  expi :: complex => complex
  "expi z == complex_of_real(exp (Re z)) * cis (Im z)"
   
end


