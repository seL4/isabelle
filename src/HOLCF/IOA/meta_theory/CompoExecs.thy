(*  Title:      HOLCF/IOA/meta_theory/CompoExecs.thy
    ID:        
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Execution level.
*)  

CompoExecs = Traces + 


consts 

 ProjA      ::"('a,'s * 't)execution => ('a,'s)execution"
 ProjA2     ::"('a,'s * 't)pairs     -> ('a,'s)pairs"
 ProjB      ::"('a,'s * 't)execution => ('a,'t)execution"
 ProjB2     ::"('a,'s * 't)pairs     -> ('a,'t)pairs"
 Filter_ex  ::"('a,'s)ioa => ('a,'s)execution => ('a,'s)execution"
 Filter_ex2 ::"('a,'s)ioa => ('a,'s)pairs     -> ('a,'s)pairs" 
 stutter    ::"('a,'s)ioa => ('a,'s)execution => bool" 
 stutter2   ::"('a,'s)ioa => ('a,'s)pairs     -> ('s => tr)"


defs 


ProjA_def
 "ProjA ex == (fst (fst ex), ProjA2`(snd ex))" 

ProjB_def
 "ProjB ex == (snd (fst ex), ProjB2`(snd ex))" 


ProjA2_def
  "ProjA2 == Map (%x.(fst x,fst(snd x)))"

ProjB2_def
  "ProjB2 == Map (%x.(fst x,snd(snd x)))"
 

Filter_ex_def
  "Filter_ex A ex == (fst ex,Filter_ex2 A`(snd ex))"


Filter_ex2_def
  "Filter_ex2 A ==  Filter (%x.fst x:act A)"

stutter_def
  "stutter A ex == ((stutter2 A`(snd ex)) (fst ex) ~= FF)"

stutter2_def
  "stutter2 A ==(fix`(LAM h ex. (%s. case ex of 
      nil => TT
    | x##xs => (flift1 
            (%p.(If Def ((fst p)~:act A)
                 then Def (s=(snd p)) 
                 else TT fi)
                andalso (h`xs) (snd p)) 
             `x)
   )))" 




end