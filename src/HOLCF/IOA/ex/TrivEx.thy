(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Müller

Trivial Abstraction Example.
*)

TrivEx = Abstraction + 

datatype action = INC

consts

C_asig   ::  "action signature"
C_trans  :: (action, nat)transition set
C_ioa    :: (action, nat)ioa

A_asig   :: "action signature"
A_trans  :: (action, bool)transition set
A_ioa    :: (action, bool)ioa

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

h_abs_def
  "h_abs n == n~=0"

rules

MC_result
  "validIOA A_ioa (<>[] <%(b,a,c). b>)"

end