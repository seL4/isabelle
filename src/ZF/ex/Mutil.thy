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

inductive
  domains "domino" <= "Pow(nat*nat)"
  intrs
    horiz  "[| i \\<in> nat;  j \\<in> nat |] ==> {<i,j>, <i,succ(j)>} \\<in> domino"
    vertl  "[| i \\<in> nat;  j \\<in> nat |] ==> {<i,j>, <succ(i),j>} \\<in> domino"
  type_intrs  empty_subsetI, cons_subsetI, PowI, SigmaI, nat_succI


inductive
    domains "tiling(A)" <= "Pow(Union(A))"
  intrs
    empty  "0 \\<in> tiling(A)"
    Un     "[| a \\<in> A;  t \\<in> tiling(A);  a Int t = 0 |] ==> a Un t \\<in> tiling(A)"
  type_intrs  empty_subsetI, Union_upper, Un_least, PowI
  type_elims "[make_elim PowD]"

constdefs
  evnodd  :: [i,i]=>i
  "evnodd(A,b) == {z \\<in> A. \\<exists>i j. z=<i,j> & (i#+j) mod 2 = b}"

end
