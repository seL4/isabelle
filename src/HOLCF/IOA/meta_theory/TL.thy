(*  Title:      HOLCF/IOA/meta_theory/TLS.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

A General Temporal Logic

*)   


		       
TL = Pred + Sequence +  

default term

types

'a temporal      = 'a Seq predicate

 
consts


suffix     :: "'a Seq => 'a Seq => bool"
tsuffix    :: "'a Seq => 'a Seq => bool"

validT     :: "'a Seq predicate => bool"

unlift     ::  "'a lift => 'a"

Init         ::"'a predicate => 'a temporal"          ("<_>" [0] 1000)

Box          ::"'a temporal => 'a temporal"   ("[] (_)" [80] 80)
Diamond      ::"'a temporal => 'a temporal"   ("<> (_)" [80] 80)
Next         ::"'a temporal => 'a temporal"   
Leadsto      ::"'a temporal => 'a temporal => 'a temporal"  (infixr "~>" 22)

syntax (symbols)
   "Box"        ::"'a temporal => 'a temporal"   ("\\<box> (_)" [80] 80)
   "Diamond"    ::"'a temporal => 'a temporal"   ("\\<diamond> (_)" [80] 80)
   "Leadsto"    ::"'a temporal => 'a temporal => 'a temporal"  (infixr "\\<leadsto>" 22)
 
defs


unlift_def
  "unlift x == (case x of 
                 Undef   => arbitrary
               | Def y   => y)"

(* this means that for nil and UU the effect is unpredictable *)
Init_def
  "Init P s ==  (P (unlift (HD$s)))" 

suffix_def
  "suffix s2 s == ? s1. (Finite s1  & s = s1 @@ s2)" 

tsuffix_def
  "tsuffix s2 s == s2 ~= nil & s2 ~= UU & suffix s2 s"

Box_def
  "([] P) s == ! s2. tsuffix s2 s --> P s2"

Next_def
  "(Next P) s == if (TL$s=UU | TL$s=nil) then (P s) else P (TL$s)"

Diamond_def
  "<> P == .~ ([] (.~ P))"

Leadsto_def
   "P ~> Q == ([] (P .--> (<> Q)))"  

validT_def
  "validT P == ! s. s~=UU & s~=nil --> (s |= P)"

end