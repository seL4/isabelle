(*  Title:      HOL/IOA/example/Spec.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The implementation of a memory.
*)

Impl = IOA + Action +


consts

impl_sig   :: "action signature"
impl_trans :: "(action, nat  * bool)transition set"
impl_ioa   :: "(action, nat * bool)ioa"

defs

sig_def "impl_sig == (UN l.{Free l} Un {New}, 
                     UN l.{Loc l}, 
                     {})"

trans_def "impl_trans ==                           
 {tr. let s = fst(tr); k = fst s; b = snd s;                            
          t = snd(snd(tr)); k' = fst t; b' = snd t                      
      in                                          
      case fst(snd(tr))                           
      of   
      New       => k' = k & b'  |                    
      Loc l     => b & l= k & k'= (Suc k) & ~b' |                    
      Free l    => k'=k & b'=b}"

ioa_def "impl_ioa == (impl_sig, {(0,False)}, impl_trans,{},{})"

end
