(*  Title:      HOL/UNITY/UNITYMisc.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Some miscellaneous and add-hoc set theory concepts.
*)



UNITYMisc = Main +
constdefs
  greaterThan :: [i,i]=> i
  "greaterThan(u,A) == {x:A. u<x}"
end