(*  Title:      HOL/UNITY/Follows
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Follows relation of Charpentier and Sivilotte

The safety conditions ensures that "givenBy f" is implementable in the
  progress part: g cannot do anything silly.
*)

Follows = ELT +

constdefs

  Follows :: "['a => 'b::{order}, 'a => 'b::{order}] => 'a program set"
                 (infixl "Fols" 65)
   "f Fols g == Increasing g Int Increasing f Int
                Always {s. f s <= g s} Int
                (INT k. {s. k <= g s} LeadsTo {s. k <= f s})"


end
