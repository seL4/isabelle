(*  Title:       IntFloor.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001,2002  University of Edinburgh
    Description: Floor and ceiling operations over reals
*)

IntFloor = Integration + 

constdefs
    
    floor :: real => int
   "floor r == (LEAST n. r < real (n + (1::int)))"

    ceiling :: real => int
    "ceiling r == - floor (- r)"
  
end
