(*  Title:      HOL/UNITY/UNITYMisc.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Some miscellaneous and add-hoc set theory concepts.
*)



UNITYMisc = Main +
constdefs
  less_than :: i=>i
  "less_than(A) == measure(A, %x. x)"

  lessThan :: [i, i] => i
  "lessThan(u,A) == {x:A. x<u}"

  greaterThan :: [i,i]=> i
  "greaterThan(u,A) == {x:A. u<x}"

  (* Identity relation over a domain A *)
  Identity :: i=>i
  "Identity(A) == {p:A*A. EX x. p=<x,x>}"
end