(*  Title:      HOLCF/IOA/meta_theory/SimCorrectness.thy
    ID:         $Id$
    Author:     Olaf Müller

Correctness of Simulations in HOLCF/IOA.
*)


SimCorrectness = Simulations + 
       
consts

  corresp_ex_sim   ::"('a,'s2)ioa => (('s1 *'s2)set) => 
                      ('a,'s1)execution => ('a,'s2)execution"
  (* Note: s2 instead of s1 in last argument type !! *)
  corresp_ex_simC  ::"('a,'s2)ioa => (('s1 * 's2)set) => ('a,'s1)pairs
                   -> ('s2 => ('a,'s2)pairs)"


defs
           
corresp_ex_sim_def
  "corresp_ex_sim A R ex == let S'= (@s'.(fst ex,s'):R & s': starts_of A)
                            in 
                               (S',(corresp_ex_simC A R$(snd ex)) S')"


corresp_ex_simC_def
  "corresp_ex_simC A R  == (fix$(LAM h ex. (%s. case ex of 
      nil =>  nil
    | x##xs => (flift1 (%pr. let a = (fst pr); t = (snd pr);
                                 T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t' 
                             in
                                (@cex. move A cex s a T')
                                 @@ ((h$xs) T'))
                        $x) )))"
 
end