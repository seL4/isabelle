(*  Title:      ComplexBin.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
    Descrition: Binary arithmetic for the complex numbers
                This case is reduced to that for the reals.
*)

ComplexBin = Complex + 


instance
  complex :: number 

instance complex :: plus_ac0(complex_add_commute,complex_add_assoc,complex_add_zero_left)


defs
  complex_number_of_def
    "number_of v == complex_of_real (number_of v)"
     (*::bin=>complex               ::bin=>complex*)

end
