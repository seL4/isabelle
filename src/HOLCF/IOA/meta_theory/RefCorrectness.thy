(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Correctness of Refinement Mappings in HOLCF/IOA
*)


RefCorrectness = RefMappings + 
   
consts

  corresp_ex   ::"('a,'s2)ioa => ('s1 => 's2) => 
                  ('a,'s1)execution => ('a,'s2)execution"
  corresp_exC  ::"('a,'s2)ioa => ('s1 => 's2) => ('a,'s1)pairs
                   -> ('s1 => ('a,'s2)pairs)"


defs

corresp_ex_def
  "corresp_ex A f ex == (f (fst ex),(corresp_exC A f`(snd ex)) (fst ex))"


corresp_exC_def
  "corresp_exC A f  == (fix`(LAM h ex. (%s. case ex of 
      nil =>  nil
    | x##xs => (flift1 (%pr. (@cex. move A cex (f s) (fst pr) (f (snd pr)))
                              @@ ((h`xs) (snd pr)))
                        `x) )))"
 


end