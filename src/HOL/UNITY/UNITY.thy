(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

UNITY = Main + 

typedef (Program)
  'a program = "{(init:: 'a set, acts :: ('a * 'a)set set,
		  allowed :: ('a * 'a)set set). Id:acts & Id: allowed}"

consts
  constrains :: "['a set, 'a set] => 'a program set"  (infixl "co"     60)
  op_unless  :: "['a set, 'a set] => 'a program set"  (infixl "unless" 60)

constdefs
    mk_program :: "('a set * ('a * 'a)set set * ('a * 'a)set set)
		   => 'a program"
    "mk_program == %(init, acts, allowed).
                      Abs_Program (init, insert Id acts, insert Id allowed)"

  Init :: "'a program => 'a set"
    "Init F == (%(init, acts, allowed). init) (Rep_Program F)"

  Acts :: "'a program => ('a * 'a)set set"
    "Acts F == (%(init, acts, allowed). acts) (Rep_Program F)"

  AllowedActs :: "'a program => ('a * 'a)set set"
    "AllowedActs F == (%(init, acts, allowed). allowed) (Rep_Program F)"

  Allowed :: "'a program => 'a program set"
    "Allowed F == {G. Acts G <= AllowedActs F}"

  stable     :: "'a set => 'a program set"
    "stable A == A co A"

  strongest_rhs :: "['a program, 'a set] => 'a set"
    "strongest_rhs F A == Inter {B. F : A co B}"

  invariant :: "'a set => 'a program set"
    "invariant A == {F. Init F <= A} Int stable A"

  (*Polymorphic in both states and the meaning of <= *)
  increasing :: "['a => 'b::{order}] => 'a program set"
    "increasing f == INT z. stable {s. z <= f s}"


defs
  constrains_def "A co B == {F. ALL act: Acts F. act^^A <= B}"

  unless_def     "A unless B == (A-B) co (A Un B)"

end
