(*  Title:      ZF/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra

Variables' types are introduced globally so that type verification
reduces to the usual ZF typechecking: an ill-tyed expressions reduce to the empty set.
*)

Mutex = SubstAx + 
consts
  p, m, n, u, v :: i
  
translations
  "p" == "Var([])"
  "m" == "Var([0])"
  "n" == "Var([1])"
  "u" == "Var([1,0])"
  "v" == "Var([1,1])"
  
rules (** Type declarations  **)
  p_type  "type_of(p)=bool"
  m_type  "type_of(m)=int"
  n_type  "type_of(n)=int"
  u_type  "type_of(u)=bool"
  v_type  "type_of(v)=bool"
  
constdefs
  (** The program for process U **)
   U0 :: i
    "U0 == {<s,t>:state*state. t = s(u:=1, m:=#1) & s`m = #0}"

  U1 :: i
  "U1 == {<s,t>:state*state. t = s(p:= s`v, m:=#2) &  s`m = #1}"

  U2 :: i
    "U2 == {<s,t>:state*state. t = s(m:=#3) & s`p=0 & s`m = #2}"

  U3 :: i
    "U3 == {<s,t>:state*state. t=s(u:=0, m:=#4) & s`m = #3}"

  U4 :: i
    "U4 == {<s,t>:state*state. t = s(p:=1, m:=#0) & s`m = #4}"

  
   (** The program for process V **)
  
  V0 :: i
    "V0 == {<s,t>:state*state. t = s (v:=1, n:=#1) & s`n = #0}"

  V1 :: i
    "V1 == {<s,t>:state*state. t = s(p:=not(s`u), n:=#2) & s`n = #1}"

  V2 :: i
    "V2 == {<s,t>:state*state. t  = s(n:=#3) & s`p=1 & s`n = #2}"

  V3 :: i
  "V3 == {<s,t>:state*state. t = s (v:=0, n:=#4) & s`n = #3}"

  V4 :: i
    "V4 == {<s,t>:state*state. t  = s (p:=0, n:=#0) & s`n = #4}"

 Mutex :: i
 "Mutex == mk_program({s:state. s`u=0 & s`v=0 & s`m = #0 & s`n = #0},
                       {U0, U1, U2, U3, U4, V0, V1, V2, V3, V4}, Pow(state*state))"

  (** The correct invariants **)

  IU :: i
    "IU == {s:state. (s`u = 1<->(#1 $<= s`m & s`m $<= #3))
	             & (s`m = #3 --> s`p=0)}"

  IV :: i
    "IV == {s:state. (s`v = 1 <-> (#1 $<= s`n & s`n $<= #3))
	              & (s`n = #3 --> s`p=1)}"

  (** The faulty invariant (for U alone) **)

  bad_IU :: i
    "bad_IU == {s:state. (s`u = 1 <-> (#1 $<= s`m & s`m  $<= #3))&
                   (#3 $<= s`m & s`m $<= #4 --> s`p=0)}"

end