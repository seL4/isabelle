(*
    Factorisation within a factorial domain
    $Id$
    Author: Clemens Ballarin, started 25 November 1997
*)

Factor = Ring +

consts
  Factorisation	:: ['a::ring, 'a list, 'a] => bool
  (* factorisation of x into a list of irred factors and a unit u *)

defs
  Factorisation_def	"Factorisation x factors u == 
                           x = foldr op* factors u &
                           (ALL a : set factors. irred a) & u dvd 1"

end
