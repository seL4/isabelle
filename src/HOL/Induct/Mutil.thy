(*  Title:      HOL/Induct/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
  Originator is Max Black, according to J A Robinson.
  Popularized as the Mutilated Checkerboard Problem by J McCarthy
*)

Mutil = Main +

consts     tiling :: "'a set set => 'a set set"
inductive "tiling A"
  intrs
    empty  "{} : tiling A"
    Un     "[| a: A;  t: tiling A;  a <= -t |] ==> a Un t : tiling A"

consts    domino :: "(nat*nat)set set"
inductive domino
  intrs
    horiz  "{(i, j), (i, Suc j)} : domino"
    vertl  "{(i, j), (Suc i, j)} : domino"

constdefs
  colored  :: "nat => (nat*nat)set"
   "colored b == {(i,j). (i+j) mod #2 = b}"

end
