(*  Title:      HOLCF/IOA/meta_theory/CompoExecs.thy
    ID:         $Id$
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
 Filter_ex  ::"'a signature => ('a,'s)execution => ('a,'s)execution"
 Filter_ex2 ::"'a signature => ('a,'s)pairs     -> ('a,'s)pairs" 
 stutter    ::"'a signature => ('a,'s)execution => bool" 
 stutter2   ::"'a signature => ('a,'s)pairs     -> ('s => tr)"

 par_execs  ::"[('a,'s)execution_module,('a,'t)execution_module] => ('a,'s*'t)execution_module"


defs 


ProjA_def
 "ProjA ex == (fst (fst ex), ProjA2$(snd ex))" 

ProjB_def
 "ProjB ex == (snd (fst ex), ProjB2$(snd ex))" 


ProjA2_def
  "ProjA2 == Map (%x.(fst x,fst(snd x)))"

ProjB2_def
  "ProjB2 == Map (%x.(fst x,snd(snd x)))"
 

Filter_ex_def
  "Filter_ex sig ex == (fst ex,Filter_ex2 sig$(snd ex))"


Filter_ex2_def
  "Filter_ex2 sig ==  Filter (%x. fst x:actions sig)"

stutter_def
  "stutter sig ex == ((stutter2 sig$(snd ex)) (fst ex) ~= FF)"

stutter2_def
  "stutter2 sig ==(fix$(LAM h ex. (%s. case ex of 
      nil => TT
    | x##xs => (flift1 
            (%p.(If Def ((fst p)~:actions sig)
                 then Def (s=(snd p)) 
                 else TT fi)
                andalso (h$xs) (snd p)) 
             $x)
   )))" 

par_execs_def
  "par_execs ExecsA ExecsB == 
       let exA = fst ExecsA; sigA = snd ExecsA; 
           exB = fst ExecsB; sigB = snd ExecsB       
       in
       (    {ex. Filter_ex sigA (ProjA ex) : exA}
        Int {ex. Filter_ex sigB (ProjB ex) : exB}
        Int {ex. stutter sigA (ProjA ex)}
        Int {ex. stutter sigB (ProjB ex)}
        Int {ex. Forall (%x. fst x:(actions sigA Un actions sigB)) (snd ex)},
        asig_comp sigA sigB)"

end