(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

(* Theory of Groups, for Sylow's theorem. F. Kammueller, 11.10.96
Step 1: Use two separate .thy files for groups  and Sylow's thm, respectively:

Besides the formalization of groups as polymorphic sets of quadruples this
theory file contains a bunch of declarations and axioms of number theory
because it is meant to be the basis for a proof experiment of the theorem of
Sylow. This theorem uses various kinds of theoretical domains.  To improve the
syntactical form I have deleted here in contrast to the first almost complete
version of the proof (8exp/Group.* or presently results/AllgGroup/Group.* )
all definitions which are specific for Sylow's theorem. They are now contained
in the file Sylow.thy.
*)

Group = Exponent +


constdefs

  carrier :: "('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a) => 'a set"
   "carrier(G) == fst(G)"
  
  bin_op  :: "('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a) => (['a, 'a] => 'a)"
   "bin_op(G)  == fst(snd(G))"
  
  invers :: "('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a) => ('a => 'a)"
"invers(G) == fst(snd(snd(G)))"
  
  unity     :: "('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a) => 'a"
 "unity(G)     == snd(snd(snd(G)))"
  
  order     :: "('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a) => nat"
   "order(G) == card(fst(G))"

  r_coset    :: "[('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a), 'a set, 'a] => 'a set"    
   "r_coset G  H  a == {b . ? h : H. bin_op G h a = b}"

  set_r_cos  :: "[('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a), 'a set] => 'a set set"

   "set_r_cos G H == {C . ? a : carrier G. C = r_coset G H a}"

  subgroup :: "['a set,('a set * (['a, 'a] => 'a) * ('a => 'a) * 'a)] => bool"
               ("_ <<= _" [51,50]50)

   "H <<= G == H <= carrier(G) & (H,bin_op(G),invers(G),unity(G)) : Group"

  Group :: "'a  set"

   "Group == {(G,f,inv,e). f : G -> G -> G & inv : G -> G & e : G &\
\                     (! x: G. ! y: G. !z: G.\
\                     (f (inv x) x = e) & (f e x = x) &
		      (f (f x y) z = f (x) (f y z)))}"

end

