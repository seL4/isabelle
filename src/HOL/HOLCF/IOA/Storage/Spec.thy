(*  Title:      HOL/HOLCF/IOA/Storage/Spec.thy
    Author:     Olaf Müller
*)

section \<open>The specification of a memory\<close>

theory Spec
imports IOA.IOA Action
begin

definition
  spec_sig :: "action signature" where
  "spec_sig = (\<Union>l.{Free l} \<union> {New},
               \<Union>l.{Loc l},
               {})"

definition
  spec_trans :: "(action, nat set \<times> bool)transition set" where
  "spec_trans =
   {tr. let s = fst(tr); used = fst s; c = snd s;
            t = snd(snd(tr)); used' = fst t; c' = snd t
        in
        case fst(snd(tr))
        of
        New       \<Rightarrow> used' = used \<and> c'  |
        Loc l     \<Rightarrow> c \<and> l \<notin> used \<and> used'= used \<union> {l} \<and> \<not>c'   |
        Free l    \<Rightarrow> used'=used - {l} \<and> c'=c}"

definition
  spec_ioa :: "(action, nat set \<times> bool)ioa" where
  "spec_ioa = (spec_sig, {({},False)}, spec_trans,{},{})"

end
