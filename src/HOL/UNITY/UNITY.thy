(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

UNITY = LessThan +

constdefs

  constrains :: "[('a * 'a)set set, 'a set, 'a set] => bool"
    "constrains Acts A B == ALL act:Acts. act^^A <= B"

  stable     :: "('a * 'a)set set => 'a set => bool"
    "stable Acts A == constrains Acts A A"

  strongest_rhs :: "[('a * 'a)set set, 'a set] => 'a set"
    "strongest_rhs Acts A == Inter {B. constrains Acts A B}"

  unless :: "[('a * 'a)set set, 'a set, 'a set] => bool"
    "unless mutex A B == constrains mutex (A-B) (A Un B)"

end
