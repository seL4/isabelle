(*  Title:      HOLCF/IOA/meta_theory/Simulations.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Simulations in HOLCF/IOA.
*)

Simulations = RefCorrectness  +

default term

consts

  is_simulation            ::"[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_backward_simulation   ::"[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_forw_back_simulation  ::"[('s1 * 's2 set)set,('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_back_forw_simulation  ::"[('s1 * 's2 set)set,('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_history_relation      ::"[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_prophecy_relation     ::"[('s1 * 's2)set,('a,'s1)ioa,('a,'s2)ioa] => bool"

defs

is_simulation_def
  "is_simulation R C A ==                          
   (!s:starts_of C. R``{s} Int starts_of A ~= {}) &        
   (!s s' t a. reachable C s &                      
               s -a--C-> t   &
               (s,s') : R              
               --> (? t' ex. (t,t'):R & move A ex s' a t'))"

is_backward_simulation_def
  "is_backward_simulation R C A ==                          
   (!s:starts_of C. R``{s} <= starts_of A) &        
   (!s t t' a. reachable C s &                      
               s -a--C-> t   &
               (t,t') : R              
               --> (? ex s'. (s,s'):R & move A ex s' a t'))"

is_forw_back_simulation_def
  "is_forw_back_simulation R C A ==                          
   (!s:starts_of C. ? S'. (s,S'):R & S'<= starts_of A) &        
   (!s S' t a. reachable C s &                      
               s -a--C-> t   &
               (s,S') : R              
               --> (? T'. (t,T'):R & (! t':T'. ? s':S'. ? ex. move A ex s' a t')))"

is_back_forw_simulation_def
  "is_back_forw_simulation R C A ==                          
   (!s:starts_of C. ! S'. (s,S'):R --> S' Int starts_of A ~={}) &        
   (!s t T' a. reachable C s &                      
               s -a--C-> t   &
               (t,T') : R              
               --> (? S'. (s,S'):R & (! s':S'. ? t':T'. ? ex. move A ex s' a t')))"

is_history_relation_def
  "is_history_relation R C A == is_simulation R C A & 
                                is_ref_map (%x.(@y. (x,y):(R^-1))) A C"

is_prophecy_relation_def
  "is_prophecy_relation R C A == is_backward_simulation R C A & 
                                 is_ref_map (%x.(@y. (x,y):(R^-1))) A C"
                      
end
