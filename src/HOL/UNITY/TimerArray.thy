(*  Title:      HOL/UNITY/TimerArray.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

TimerArray = PPROD +

constdefs
  Timer :: nat program
    "Timer == mk_program (UNIV, {range(%n. (Suc n, n))})"

end
