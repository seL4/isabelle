(*  Title:      HOL/Lex/RegSet_of_nat_DA.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Conversion of deterministic automata into regular sets.

To generate a regual expression, the alphabet must be finite.
regexp needs to be supplied with an 'a list for a unique order

add_Atom d i j r a = (if d a i = j then Union r (Atom a) else r)
atoms d i j as = foldl (add_Atom d i j) Empty as

regexp as d i j 0 = (if i=j then Union (Star Empty) (atoms d i j as)
                        else atoms d i j as
*)

RegSet_of_nat_DA = RegSet + DA +

types 'a nat_next = "'a => nat => nat"

syntax deltas :: 'a nat_next => 'a list => nat => nat
translations "deltas" == "foldl2"

consts trace :: 'a nat_next => nat => 'a list => nat list
primrec trace list
"trace d i [] = []"
"trace d i (x#xs) = d x i # trace d (d x i) xs"

(* conversion a la Warshall *)

consts regset :: 'a nat_next => nat => nat => nat => 'a list set
primrec regset nat
"regset d i j 0 = (if i=j then insert [] {[a] | a. d a i = j}
                          else {[a] | a. d a i = j})"
"regset d i j (Suc k) = regset d i j k Un
                        conc (regset d i k k)
                             (conc (star(regset d k k k))
                                   (regset d k j k))"

constdefs
 regset_of_DA :: ('a,nat)da => nat => 'a list set
"regset_of_DA A k == UN j:{j. j<k & fin A j}. regset (next A) (start A) j k"

 bounded :: "'a => nat => bool"
"bounded d k == !n. n < k --> (!x. d x n < k)"

end
