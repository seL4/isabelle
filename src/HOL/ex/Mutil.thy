(*  Title:      HOL/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Checkerboard Problem, formalized inductively
*)

Mutil = Finite +
consts
  below   :: nat => nat set
  evnodd  :: "[(nat*nat)set, nat] => (nat*nat)set"
  domino  :: "(nat*nat)set set"
  tiling  :: 'a set set => 'a set set

defs
  below_def  "below n    == nat_rec n {} insert"
  evnodd_def "evnodd A b == A Int {(i,j). (i+j) mod 2 = b}"

inductive "domino"
  intrs
    horiz  "{(i, j), (i, Suc j)} : domino"
    vertl  "{(i, j), (Suc i, j)} : domino"

inductive "tiling A"
  intrs
    empty  "{} : tiling A"
    Un     "[| a: A;  t: tiling A;  a Int t = {} |] ==> a Un t : tiling A"

end
