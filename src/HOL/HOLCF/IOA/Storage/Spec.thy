(*  Title:      HOL/HOLCF/IOA/Storage/Spec.thy
    Author:     Olaf Müller
*)

section {* The specification of a memory *}

theory Spec
imports IOA Action
begin

definition
  spec_sig :: "action signature" where
  "spec_sig = (UN l.{Free l} Un {New},
               UN l.{Loc l},
               {})"

definition
  spec_trans :: "(action, nat set * bool)transition set" where
  "spec_trans =
   {tr. let s = fst(tr); used = fst s; c = snd s;
            t = snd(snd(tr)); used' = fst t; c' = snd t
        in
        case fst(snd(tr))
        of
        New       => used' = used & c'  |
        Loc l     => c & l~:used  & used'= used Un {l} & ~c'   |
        Free l    => used'=used - {l} & c'=c}"

definition
  spec_ioa :: "(action, nat set * bool)ioa" where
  "spec_ioa = (spec_sig, {({},False)}, spec_trans,{},{})"

end
