(*  Title:      HOLCF/IOA/meta_theory/RefMappings.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Refinement Mappings in HOLCF/IOA
*)

RefMappings = Traces  +

default term

consts

  move         ::"[('a,'s)ioa,('a,'s)pairs,'s,'a,'s] => bool"
  is_ref_map   ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool"
  is_weak_ref_map ::"[('s1=>'s2),('a,'s1)ioa,('a,'s2)ioa] => bool"
 

defs


move_def
  "move ioa ex s a t ==    
    (is_exec_frag ioa (s,ex) &  Finite ex & 
     laststate (s,ex)=t  &     
     mk_trace ioa$ex = (if a:ext(ioa) then a>>nil else nil))"

is_ref_map_def
  "is_ref_map f C A ==                          
   (!s:starts_of(C). f(s):starts_of(A)) &        
   (!s t a. reachable C s &                      
            s -a--C-> t                 
            --> (? ex. move A ex (f s) a (f t)))"
 
is_weak_ref_map_def
  "is_weak_ref_map f C A ==                          
   (!s:starts_of(C). f(s):starts_of(A)) &        
   (!s t a. reachable C s &                      
            s -a--C-> t     
            --> (if a:ext(C) 
                 then (f s) -a--A-> (f t)
                 else (f s)=(f t)))" 


end
