(*
    Prepearing definitions for polynomials
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
*)

ProtoPoly = Abstract +

consts
  bound :: [nat, nat => 'a::ringS] => bool

defs
  bound_def  "bound n f == ALL i. n<i --> f i = <0>"

end
