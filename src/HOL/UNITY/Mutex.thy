(*  Title:      HOL/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

Mutex = Update + UNITY + Traces + SubstAx +

(*WE NEED A GENERAL TREATMENT OF NUMBERS!!*)
syntax
  "3"       :: nat                ("3")
  "4"       :: nat                ("4")

translations
   "3"  == "Suc 2"
   "4"  == "Suc 3"


(*program variables*)
datatype pvar = PP | MM | NN | UU | VV

(*No booleans; instead True=1 and False=0*)
types state = pvar => nat

constdefs
  cmd0 :: "[pvar,pvar] => (state*state) set"
    "cmd0 u m == {(s,s'). s' = s[u|->1][m|->1] & s m = 0}"

  cmd1u :: "(state*state) set"
    "cmd1u == {(s,s'). s' = s[PP|-> s VV][MM|->2] & s MM = 1}"

  cmd1v :: "(state*state) set"
    "cmd1v == {(s,s'). s' = s[PP|-> 1 - s UU][NN|->2] & s NN = 1}"

  (*Put pv=0 for u's program and pv=1 for v's program*)
  cmd2 :: "[nat,pvar] => (state*state) set"
    "cmd2 pv m == {(s,s'). s' = s[m|->3] & s PP = pv & s m = 2}"

  cmd3 :: "[pvar,pvar] => (state*state) set"
    "cmd3 u m == {(s,s'). s' = s[u|->0][m|->4] & s m = 3}"

  (*Put pv=1 for u's program and pv=0 for v's program*)
  cmd4 :: "[nat,pvar] => (state*state) set"
    "cmd4 pv m == {(s,s'). s' = s[PP|->pv][m|->0] & s m = 4}"

  mutex :: "(state*state) set set"
    "mutex == {id,
	       cmd0 UU MM, cmd0 VV NN,
	       cmd1u, cmd1v,
	       cmd2 0 MM, cmd2 1 NN,
	       cmd3 UU MM, cmd3 VV NN,
	       cmd4 1 MM, cmd4 0 NN}"

  MInit :: "state set"
    "MInit == {s. s PP < 2 & s UU = 0 & s VV = 0 & s MM = 0 & s NN = 0}"

  boolVars :: "state set"
    "boolVars == {s. s PP<2 & s UU < 2 & s VV < 2}"

  (*Put pv=0 for u's program and pv=1 for v's program*)
  invariant :: "[nat,pvar,pvar] => state set"
    "invariant pv u m == {s. ((s u=1) = (1 <= s m & s m <= 3)) &
			     (s m = 3 --> s PP = pv)}"

  bad_invariant :: "[nat,pvar,pvar] => state set"
    "bad_invariant pv u m == {s. ((s u=1) = (1 <= s m & s m <= 3)) &
			         (3 <= s m & s m <= 4 --> s PP = pv)}"


  

end
