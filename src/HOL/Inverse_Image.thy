(*  Title:      HOL/Inverse_Image.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Inverse image of a function
*)

Inverse_Image = Set +

constdefs
  vimage :: ['a => 'b, 'b set] => ('a set)   (infixr "-`" 90)
    "f-`B  == {x. f(x) : B}"

end
