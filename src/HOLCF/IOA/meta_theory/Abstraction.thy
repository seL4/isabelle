(*  Title:      HOLCF/IOA/meta_theory/Abstraction.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Abstraction Theory -- tailored for I/O automata
*)   

		       
Abstraction = LiveIOA + 

default term


consts

  cex_abs      ::"('s1 => 's2) => ('a,'s1)execution => ('a,'s2)execution"
  cex_absSeq   ::"('s1 => 's2) => ('a option,'s1)transition Seq => ('a option,'s2)transition Seq"

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
  "cex_abs f ex == (f (fst ex), Map (%(a,t). (a,f t))$(snd ex))"

(* equals cex_abs on Sequneces -- after ex2seq application -- *)
cex_absSeq_def
  "cex_absSeq f == % s. Map (%(s,a,t). (f s,a,f t))$s"

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

(* thm about ex2seq which is not provable by induction as ex2seq is not continous *)
ex2seq_abs_cex
  "ex2seq (cex_abs h ex) = cex_absSeq h (ex2seq ex)" 

(* analog to the proved thm strength_Box - proof skipped as trivial *)
weak_Box
"temp_weakening P Q h 
 ==> temp_weakening ([] P) ([] Q) h"

(* analog to the proved thm strength_Next - proof skipped as trivial *)
weak_Next
"temp_weakening P Q h 
 ==> temp_weakening (Next P) (Next Q) h"

end