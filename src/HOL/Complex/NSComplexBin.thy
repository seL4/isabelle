(*  Title:      NSComplexBin.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh
    Descrition: Binary arithmetic for the nonstandard complex numbers
                This case is reduced to that for the complexes (hence reals).
*)

NSComplexBin = NSComplex + 


instance
  hcomplex :: number 

defs
  hcomplex_number_of_def
    "number_of v == hcomplex_of_complex (number_of v)"
     (*::bin=>complex               ::bin=>complex*)

end