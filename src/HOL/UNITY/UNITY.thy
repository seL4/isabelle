(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

UNITY = Traces + Prefix +

constdefs

  constrains :: "['a set, 'a set] => 'a program set"
    "constrains A B == {F. ALL act: Acts F. act^^A <= B}"

  stable     :: "'a set => 'a program set"
    "stable A == constrains A A"

  strongest_rhs :: "['a program, 'a set] => 'a set"
    "strongest_rhs F A == Inter {B. F : constrains A B}"

  unless :: "['a set, 'a set] => 'a program set"
    "unless A B == constrains (A-B) (A Un B)"

  (*The traditional word for inductive properties.  Anyway, INDUCTIVE is
    reserved!*)
  invariant :: "'a set => 'a program set"
    "invariant A == {F. Init F <= A} Int stable A"

  (*Safety properties*)
  always :: "'a set => 'a program set"
    "always A == {F. reachable F <= A}"

  (*Polymorphic in both states and the meaning of <= *)
  increasing :: "['a => 'b::{ord}] => 'a program set"
    "increasing f == INT z. stable {s. z <= f s}"

end
