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
    "constrains acts A B == ALL act:acts. act^^A <= B"

  stable     :: "('a * 'a)set set => 'a set => bool"
    "stable acts A == constrains acts A A"

  strongest_rhs :: "[('a * 'a)set set, 'a set] => 'a set"
    "strongest_rhs acts A == Inter {B. constrains acts A B}"

  unless :: "[('a * 'a)set set, 'a set, 'a set] => bool"
    "unless acts A B == constrains acts (A-B) (A Un B)"

end
