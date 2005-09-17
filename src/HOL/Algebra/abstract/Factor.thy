(*
    Factorisation within a factorial domain
    $Id$
    Author: Clemens Ballarin, started 25 November 1997
*)

theory Factor imports Ring begin

constdefs
  Factorisation :: "['a::ring, 'a list, 'a] => bool"
  (* factorisation of x into a list of irred factors and a unit u *)
  "Factorisation x factors u ==
     x = foldr op* factors u &
     (ALL a : set factors. irred a) & u dvd 1"

end
