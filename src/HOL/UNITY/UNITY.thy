(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

UNITY = LessThan + Prefix +


typedef (Program)
  'a program = "{(init:: 'a set, acts :: ('a * 'a)set set). Id:acts}"

consts
  co, unless :: "['a set, 'a set] => 'a program set"       (infixl 60)

constdefs
    mk_program :: "('a set * ('a * 'a)set set) => 'a program"
    "mk_program == %(init, acts). Abs_Program (init, insert Id acts)"

  Init :: "'a program => 'a set"
    "Init F == (%(init, acts). init) (Rep_Program F)"

  Acts :: "'a program => ('a * 'a)set set"
    "Acts F == (%(init, acts). acts) (Rep_Program F)"

  stable     :: "'a set => 'a program set"
    "stable A == A co A"

  strongest_rhs :: "['a program, 'a set] => 'a set"
    "strongest_rhs F A == Inter {B. F : A co B}"

  invariant :: "'a set => 'a program set"
    "invariant A == {F. Init F <= A} Int stable A"

  (*Polymorphic in both states and the meaning of <= *)
  increasing :: "['a => 'b::{ord}] => 'a program set"
    "increasing f == INT z. stable {s. z <= f s}"


defs
  constrains_def "A co B == {F. ALL act: Acts F. act^^A <= B}"

  unless_def     "A unless B == (A-B) co (A Un B)"

end
