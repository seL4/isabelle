(*  Title:      HOL/UNITY/TimerArray.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

TimerArray = PPROD +

types 'a state = "nat * 'a"   (*second component allows new variables*)

constdefs
  count  :: "'a state => nat"
    "count s == fst s"
  
  decr  :: "('a state * 'a state) set"
    "decr == UN n uu. {((Suc n, uu), (n,uu))}"
  
  Timer :: 'a state program
    "Timer == mk_program (UNIV, {decr})"

end
