(*  Title:      HOL/IOA/example/Spec.thy
    ID:         $Id$
    Author:     Olaf Müller

The specification of a memory.
*)

Spec = IOA + Action +


consts

spec_sig   :: "action signature"
spec_trans :: "(action, nat set * bool)transition set"
spec_ioa   :: "(action, nat set * bool)ioa"

defs

sig_def "spec_sig == (UN l.{Free l} Un {New}, 
                     UN l.{Loc l}, 
                     {})"

trans_def "spec_trans ==                           
 {tr. let s = fst(tr); used = fst s; c = snd s;                            
          t = snd(snd(tr)); used' = fst t; c' = snd t                      
      in                                          
      case fst(snd(tr))                           
      of   
      New       => used' = used & c'  |                    
      Loc l     => c & l~:used  & used'= used Un {l} & ~c'   |                    
      Free l    => used'=used - {l} & c'=c}"

ioa_def "spec_ioa == (spec_sig, {({},False)}, spec_trans,{},{})"

end
