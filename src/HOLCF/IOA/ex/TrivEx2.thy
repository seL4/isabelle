(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Müller

Trivial Abstraction Example with fairness.
*)

TrivEx2 = Abstraction + IOA +

datatype action = INC

consts

C_asig   ::  "action signature"
C_trans  :: (action, nat)transition set
C_ioa    :: (action, nat)ioa
C_live_ioa :: (action, nat)live_ioa

A_asig   :: "action signature"
A_trans  :: (action, bool)transition set
A_ioa    :: (action, bool)ioa
A_live_ioa :: (action, bool)live_ioa

h_abs    :: "nat => bool"

defs

C_asig_def
  "C_asig == ({},{INC},{})"

C_trans_def "C_trans ==                                           
 {tr. let s = fst(tr);                                               
          t = snd(snd(tr))                                           
      in case fst(snd(tr))                                           
      of                                                             
      INC       => t = Suc(s)}"

C_ioa_def "C_ioa == 
 (C_asig, {0}, C_trans,{},{})"

C_live_ioa_def 
  "C_live_ioa == (C_ioa, WF C_ioa {INC})"

A_asig_def
  "A_asig == ({},{INC},{})"

A_trans_def "A_trans ==                                           
 {tr. let s = fst(tr);                                               
          t = snd(snd(tr))                                           
      in case fst(snd(tr))                                           
      of                                                             
      INC       => t = True}"

A_ioa_def "A_ioa == 
 (A_asig, {False}, A_trans,{},{})"

A_live_ioa_def 
  "A_live_ioa == (A_ioa, WF A_ioa {INC})"



h_abs_def
  "h_abs n == n~=0"

rules

MC_result
  "validLIOA (A_ioa,WF A_ioa {INC}) (<>[] <%(b,a,c). b>)"

end