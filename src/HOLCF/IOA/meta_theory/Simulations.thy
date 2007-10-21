(*  Title:      HOLCF/IOA/meta_theory/Simulations.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Simulations in HOLCF/IOA *}

theory Simulations
imports RefCorrectness
begin

defaultsort type

definition
  is_simulation :: "[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_simulation R C A =
   ((!s:starts_of C. R``{s} Int starts_of A ~= {}) &
   (!s s' t a. reachable C s &
               s -a--C-> t   &
               (s,s') : R
               --> (? t' ex. (t,t'):R & move A ex s' a t')))"

definition
  is_backward_simulation :: "[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_backward_simulation R C A =
   ((!s:starts_of C. R``{s} <= starts_of A) &
   (!s t t' a. reachable C s &
               s -a--C-> t   &
               (t,t') : R
               --> (? ex s'. (s,s'):R & move A ex s' a t')))"

definition
  is_forw_back_simulation :: "[('s1 * 's2 set)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_forw_back_simulation R C A =
   ((!s:starts_of C. ? S'. (s,S'):R & S'<= starts_of A) &
   (!s S' t a. reachable C s &
               s -a--C-> t   &
               (s,S') : R
               --> (? T'. (t,T'):R & (! t':T'. ? s':S'. ? ex. move A ex s' a t'))))"

definition
  is_back_forw_simulation :: "[('s1 * 's2 set)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_back_forw_simulation R C A =
   ((!s:starts_of C. ! S'. (s,S'):R --> S' Int starts_of A ~={}) &
   (!s t T' a. reachable C s &
               s -a--C-> t   &
               (t,T') : R
               --> (? S'. (s,S'):R & (! s':S'. ? t':T'. ? ex. move A ex s' a t'))))"

definition
  is_history_relation :: "[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_history_relation R C A = (is_simulation R C A &
                                is_ref_map (%x.(@y. (x,y):(R^-1))) A C)"

definition
  is_prophecy_relation :: "[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool" where
  "is_prophecy_relation R C A = (is_backward_simulation R C A &
                                 is_ref_map (%x.(@y. (x,y):(R^-1))) A C)"


lemma set_non_empty: "(A~={}) = (? x. x:A)"
apply auto
done

lemma Int_non_empty: "(A Int B ~= {}) = (? x. x: A & x:B)"
apply (simp add: set_non_empty)
done


lemma Sim_start_convert:
"(R``{x} Int S ~= {}) = (? y. (x,y):R & y:S)"
apply (unfold Image_def)
apply (simp add: Int_non_empty)
done

declare Sim_start_convert [simp]


lemma ref_map_is_simulation:
"!! f. is_ref_map f C A ==> is_simulation {p. (snd p) = f (fst p)} C A"

apply (unfold is_ref_map_def is_simulation_def)
apply simp
done

end
