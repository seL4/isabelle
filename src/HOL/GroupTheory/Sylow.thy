(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

(* Theory file for the proof of Sylow's theorem. F. Kammueller 11.10.96
Step 1: Use two separate .thy files for groups  and Sylow's thm, respectively:

I.e. here are the definitions which are specific for Sylow's theorem.
*)

Sylow = Group +

types i
arities i::term

consts 
  G :: "i set * ([i, i] => i) * (i => i) * i"
(*  overloading for the carrier of G does not work because "duplicate declaration" : G :: "i set" *)
  p, a, m :: "nat"
  r_cos      :: "[i set, i] => i set"   ("_ #> _" [60,61]60)
  "##"       :: "[i, i] => i"            (infixl 60)

  (* coset and bin_op short forms *)
defs 
  r_coset_abbr  "H #> x == r_coset G H x" 
  bin_op_abbr   "x ## y  == bin_op G x y"

constdefs
  e   :: "i"  "e == unity G"
  inv :: "i => i" "inv == invers G"
  calM      :: "i set set"
   "calM == {s. s <= carrier(G) & card(s) = (p ^ a)}"
  RelM      ::  "(i set * i set)set"
   "RelM  == {(N1,N2).(N1,N2): calM <*> calM & (? g: carrier(G). N1 =  (N2 #> g) )}"

rules
(* specific rules modeling the section mechanism *)
p1    "p : prime"
p2    "G : Group"
p3    "order(G) = (p ^ a) * m"
p4    "finite (carrier G)"

end
