(*  Title:      HOL/UNITY/LessThan
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

lessThan, greaterThan, atLeast, atMost

Could generalize to any linear ordering?
*)

LessThan = Main +

constdefs

  (*MOVE TO RELATION.THY??*)
  Restrict :: "[ 'a set, ('a*'b) set] => ('a*'b) set"
    "Restrict A r == r Int (A Times UNIV)"

  lessThan   :: "nat => nat set"
     "lessThan n == {i. i<n}"

  atMost   :: "nat => nat set"
     "atMost n == {i. i<=n}"
 
  greaterThan   :: "nat => nat set"
     "greaterThan n == {i. n<i}"

  atLeast   :: "nat => nat set"
     "atLeast n == {i. n<=i}"

end
