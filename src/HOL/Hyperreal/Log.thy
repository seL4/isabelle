(*  Title       : Log.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
    Description : standard logarithms only 
*)

Log = Transcendental +

constdefs

    (* power function with exponent a *)
    powr  :: [real,real] => real     (infixr 80)
    "x powr a == exp(a * ln x)"

    (* logarithm of x to base a *)
    log :: [real,real] => real
    "log a x == ln x / ln a"

end
