(*  Title:      HOL/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

Mutex = SubstAx +

record state =
  PP :: bool
  MM :: int
  NN :: int
  UU :: bool
  VV :: bool

constdefs
  
  (** The program for process U **)
  
  cmd0U :: "(state*state) set"
    "cmd0U == {(s,s'). s' = s (|UU:=True, MM:=#1|) & MM s = #0}"

  cmd1U :: "(state*state) set"
    "cmd1U == {(s,s'). s' = s (|PP:= VV s, MM:=#2|) & MM s = #1}"

  cmd2U :: "(state*state) set"
    "cmd2U == {(s,s'). s' = s (|MM:=#3|) & ~ PP s & MM s = #2}"

  cmd3U :: "(state*state) set"
    "cmd3U == {(s,s'). s' = s (|UU:=False, MM:=#4|) & MM s = #3}"

  cmd4U :: "(state*state) set"
    "cmd4U == {(s,s'). s' = s (|PP:=True, MM:=#0|) & MM s = #4}"

  (** The program for process V **)
  
  cmd0V :: "(state*state) set"
    "cmd0V == {(s,s'). s' = s (|VV:=True, NN:=#1|) & NN s = #0}"

  cmd1V :: "(state*state) set"
    "cmd1V == {(s,s'). s' = s (|PP:= ~ UU s, NN:=#2|) & NN s = #1}"

  cmd2V :: "(state*state) set"
    "cmd2V == {(s,s'). s' = s (|NN:=#3|) & PP s & NN s = #2}"

  cmd3V :: "(state*state) set"
    "cmd3V == {(s,s'). s' = s (|VV:=False, NN:=#4|) & NN s = #3}"

  cmd4V :: "(state*state) set"
    "cmd4V == {(s,s'). s' = s (|PP:=False, NN:=#0|) & NN s = #4}"

  Mprg :: state program
    "Mprg == mk_program ({s. ~ UU s & ~ VV s & MM s = #0 & NN s = #0},
			 {cmd0U, cmd1U, cmd2U, cmd3U, cmd4U, 
			  cmd0V, cmd1V, cmd2V, cmd3V, cmd4V})"


  (** The correct invariants **)

  invariantU :: "state set"
    "invariantU == {s. (UU s = (#1 <= MM s & MM s <= #3)) &
		       (MM s = #3 --> ~ PP s)}"

  invariantV :: "state set"
    "invariantV == {s. (VV s = (#1 <= NN s & NN s <= #3)) &
		       (NN s = #3 --> PP s)}"

  (** The faulty invariant (for U alone) **)

  bad_invariantU :: "state set"
    "bad_invariantU == {s. (UU s = (#1 <= MM s & MM s <= #3)) &
		           (#3 <= MM s & MM s <= #4 --> ~ PP s)}"

end
