(*  Title:      ZF/ex/Mutil
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

The Mutilated Chess Board Problem, formalized inductively
  Originator is Max Black, according to J A Robinson.
  Popularized as the Mutilated Checkerboard Problem by J McCarthy
*)

Mutil = CardinalArith +
consts
  domino  :: i
  tiling  :: i=>i
  evnodd  :: [i,i]=>i

inductive
  domains "domino" <= "Pow(nat*nat)"
  intrs
    horiz  "[| i: nat;  j: nat |] ==> {<i,j>, <i,succ(j)>} : domino"
    vertl  "[| i: nat;  j: nat |] ==> {<i,j>, <succ(i),j>} : domino"
  type_intrs "[empty_subsetI, cons_subsetI, PowI, SigmaI, nat_succI]"


inductive
    domains "tiling(A)" <= "Pow(Union(A))"
  intrs
    empty  "0 : tiling(A)"
    Un     "[| a: A;  t: tiling(A);  a Int t = 0 |] ==> a Un t : tiling(A)"
  type_intrs "[empty_subsetI, Union_upper, Un_least, PowI]"
  type_elims "[make_elim PowD]"

defs
  evnodd_def "evnodd(A,b) == {z:A. EX i j. z=<i,j> & (i#+j) mod 2 = b}"

end
