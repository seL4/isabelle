(*  Title:      HOLCF/IOA/meta_theory/Abstraction.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Abstraction Theory -- tailored for I/O automata
*)   

		       
Abstraction = LiveIOA + TLS + 

default term


consts

  cex_abs   ::"('s1 => 's2) => ('a,'s1)execution => ('a,'s2)execution"

  is_abstraction ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool"

  weakeningIOA       :: "('a,'s2)ioa => ('a,'s1)ioa => ('s1 => 's2) => bool" 
  temp_weakening     :: "('a,'s2)ioa_temp => ('a,'s1)ioa_temp => ('s1 => 's2) => bool" 
  temp_strengthening :: "('a,'s2)ioa_temp => ('a,'s1)ioa_temp => ('s1 => 's2) => bool" 

  state_weakening       :: "('a,'s2)step_pred => ('a,'s1)step_pred => ('s1 => 's2) => bool"
  state_strengthening   :: "('a,'s2)step_pred => ('a,'s1)step_pred => ('s1 => 's2) => bool"

  is_live_abstraction  :: "('s1 => 's2) => ('a,'s1)live_ioa => ('a,'s2)live_ioa => bool"


defs

is_abstraction_def
  "is_abstraction f C A ==                          
   (!s:starts_of(C). f(s):starts_of(A)) &        
   (!s t a. reachable C s & s -a--C-> t     
            --> (f s) -a--A-> (f t))"

is_live_abstraction_def
  "is_live_abstraction h CL AM == 
      is_abstraction h (fst CL) (fst AM) &
      temp_weakening (snd AM) (snd CL) h"

cex_abs_def
  "cex_abs f ex == (f (fst ex), Map (%(a,t). (a,f t))`(snd ex))"

weakeningIOA_def
   "weakeningIOA A C h == ! ex. ex : executions C --> cex_abs h ex : executions A"

temp_weakening_def
   "temp_weakening Q P h == temp_strengthening (.~ Q) (.~ P) h"

temp_strengthening_def
   "temp_strengthening Q P h == ! ex. (cex_abs h ex |== Q) --> (ex |== P)"

state_weakening_def
  "state_weakening Q P h == state_strengthening (.~Q) (.~P) h"

state_strengthening_def
  "state_strengthening Q P h == ! s t a.  Q (h(s),a,h(t)) --> P (s,a,t)"

rules

strength_Init
 "state_strengthening P Q h 
  ==> temp_strengthening (Init P) (Init Q) h"

strength_Box
"temp_strengthening P Q h 
 ==> temp_strengthening ([] P) ([] Q) h"

strength_Next
"temp_strengthening P Q h 
 ==> temp_strengthening (Next P) (Next Q) h"

weak_Init
 "state_weakening P Q h 
  ==> temp_weakening (Init P) (Init Q) h"

weak_Box
"temp_weakening P Q h 
 ==> temp_weakening ([] P) ([] Q) h"

weak_Next
"temp_weakening P Q h 
 ==> temp_weakening (Next P) (Next Q) h"

end