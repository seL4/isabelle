(*  Title:      HOL/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
  Originator is Max Black, according to J A Robinson.
  Popularized as the Mutilated Checkerboard Problem by J McCarthy
*)

Mutil = Finite +
consts
  domino  :: "(nat*nat)set set"
  tiling  :: 'a set set => 'a set set
  below   :: nat => nat set
  evnodd  :: "[(nat*nat)set, nat] => (nat*nat)set"

inductive domino
  intrs
    horiz  "{(i, j), (i, Suc j)} : domino"
    vertl  "{(i, j), (Suc i, j)} : domino"

inductive "tiling A"
  intrs
    empty  "{} : tiling A"
    Un     "[| a: A;  t: tiling A;  a Int t = {} |] ==> a Un t : tiling A"

defs
  below_def  "below n    == nat_rec {} insert n"
  evnodd_def "evnodd A b == A Int {(i,j). (i+j) mod 2 = b}"

end
