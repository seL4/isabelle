(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.thy
    ID:         $$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Correctness of Refinement Mappings in HOLCF/IOA
*)


RefCorrectness = RefMappings + 

consts

  corresp_ex   ::"('a,'s2)ioa => ('s1 => 's2) => 
                  ('a,'s1)execution => ('a,'s2)execution"
  corresp_ex2  ::"('a,'s2)ioa => ('s1 => 's2) => ('a,'s1)pairs
                   -> ('s2 => ('a,'s2)pairs)"


defs

corresp_ex_def
  "corresp_ex A f ex == (f (fst ex),(corresp_ex2 A f`(snd ex)) (f (fst ex)))"


corresp_ex2_def
  "corresp_ex2 A f  == (fix`(LAM h ex. (%s. case ex of 
      nil =>  nil
    | x##xs => (flift1 (%pr. (snd(@cex. move A cex s (fst pr) (f (snd pr))))
                              @@ ((h`xs) (f (snd pr))))
                        `x) )))"
 


end