(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Correctness of Refinement Mappings in HOLCF/IOA.
*)


RefCorrectness = RefMappings + 
   
consts

  corresp_ex   ::"('a,'s2)ioa => ('s1 => 's2) => 
                  ('a,'s1)execution => ('a,'s2)execution"
  corresp_exC  ::"('a,'s2)ioa => ('s1 => 's2) => ('a,'s1)pairs
                   -> ('s1 => ('a,'s2)pairs)"
  is_fair_ref_map  :: "('s1 => 's2) => ('a,'s1)ioa => ('a,'s2)ioa => bool"

defs

corresp_ex_def
  "corresp_ex A f ex == (f (fst ex),(corresp_exC A f$(snd ex)) (fst ex))"


corresp_exC_def
  "corresp_exC A f  == (fix$(LAM h ex. (%s. case ex of 
      nil =>  nil
    | x##xs => (flift1 (%pr. (@cex. move A cex (f s) (fst pr) (f (snd pr)))
                              @@ ((h$xs) (snd pr)))
                        $x) )))"
 
is_fair_ref_map_def
  "is_fair_ref_map f C A == 
       is_ref_map f C A &
       (! ex : executions(C). fair_ex C ex --> fair_ex A (corresp_ex A f ex))"



rules
(* Axioms for fair trace inclusion proof support, not for the correctness proof
   of refinement mappings ! 
   Note: Everything is superseded by LiveIOA.thy! *)

corresp_laststate
  "Finite ex ==> laststate (corresp_ex A f (s,ex)) = f (laststate (s,ex))"

corresp_Finite
  "Finite (snd (corresp_ex A f (s,ex))) = Finite ex"

FromAtoC
  "fin_often (%x. P (snd x)) (snd (corresp_ex A f (s,ex))) ==> fin_often (%y. P (f (snd y))) ex"

FromCtoA
  "inf_often (%y. P (fst y)) ex ==> inf_often (%x. P (fst x)) (snd (corresp_ex A f (s,ex)))"


(* Proof by case on inf W in ex: If so, ok. If not, only fin W in ex, ie there is
   an index i from which on no W in ex. But W inf enabled, ie at least once after i
   W is enabled. As W does not occur after i and W is enabling_persistent, W keeps
   enabled until infinity, ie. indefinitely *)
persistent
  "[|inf_often (%x. Enabled A W (snd x)) ex; en_persistent A W|]
   ==> inf_often (%x. fst x :W) ex | fin_often (%x. ~Enabled A W (snd x)) ex"

infpostcond
  "[| is_exec_frag A (s,ex); inf_often (%x. fst x:W) ex|]
    ==> inf_often (% x. set_was_enabled A W (snd x)) ex"

end