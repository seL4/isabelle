(*  Title:      HOL/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

Mutex = SubstAx +

record state =
  p :: bool
  m :: int
  n :: int
  u :: bool
  v :: bool

types command = "(state*state) set"

constdefs
  
  (** The program for process U **)
  
  U0 :: command
    "U0 == {(s,s'). s' = s (|u:=True, m:=Numeral1|) & m s = Numeral0}"

  U1 :: command
    "U1 == {(s,s'). s' = s (|p:= v s, m:=2|) & m s = Numeral1}"

  U2 :: command
    "U2 == {(s,s'). s' = s (|m:=3|) & ~ p s & m s = 2}"

  U3 :: command
    "U3 == {(s,s'). s' = s (|u:=False, m:=4|) & m s = 3}"

  U4 :: command
    "U4 == {(s,s'). s' = s (|p:=True, m:=Numeral0|) & m s = 4}"

  (** The program for process V **)
  
  V0 :: command
    "V0 == {(s,s'). s' = s (|v:=True, n:=Numeral1|) & n s = Numeral0}"

  V1 :: command
    "V1 == {(s,s'). s' = s (|p:= ~ u s, n:=2|) & n s = Numeral1}"

  V2 :: command
    "V2 == {(s,s'). s' = s (|n:=3|) & p s & n s = 2}"

  V3 :: command
    "V3 == {(s,s'). s' = s (|v:=False, n:=4|) & n s = 3}"

  V4 :: command
    "V4 == {(s,s'). s' = s (|p:=False, n:=Numeral0|) & n s = 4}"

  Mutex :: state program
    "Mutex == mk_program ({s. ~ u s & ~ v s & m s = Numeral0 & n s = Numeral0},
		 	  {U0, U1, U2, U3, U4, V0, V1, V2, V3, V4},
			  UNIV)"


  (** The correct invariants **)

  IU :: state set
    "IU == {s. (u s = (Numeral1 <= m s & m s <= 3)) & (m s = 3 --> ~ p s)}"

  IV :: state set
    "IV == {s. (v s = (Numeral1 <= n s & n s <= 3)) & (n s = 3 --> p s)}"

  (** The faulty invariant (for U alone) **)

  bad_IU :: state set
    "bad_IU == {s. (u s = (Numeral1 <= m s & m s <= 3)) &
	           (3 <= m s & m s <= 4 --> ~ p s)}"

end
