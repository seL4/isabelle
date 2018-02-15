(*  Title:      HOL/HOLCF/IOA/Storage/Impl.thy
    Author:     Olaf Müller
*)

section \<open>The implementation of a memory\<close>

theory Impl
imports IOA.IOA Action
begin

definition
  impl_sig :: "action signature" where
  "impl_sig = (\<Union>l.{Free l} \<union> {New},
               \<Union>l.{Loc l},
               {})"

definition
  impl_trans :: "(action, nat  * bool)transition set" where
  "impl_trans =
    {tr. let s = fst(tr); k = fst s; b = snd s;
             t = snd(snd(tr)); k' = fst t; b' = snd t
         in
         case fst(snd(tr))
         of
         New       \<Rightarrow> k' = k \<and> b'  |
         Loc l     \<Rightarrow> b \<and> l= k \<and> k'= (Suc k) \<and> \<not>b' |
         Free l    \<Rightarrow> k'=k \<and> b'=b}"

definition
  impl_ioa :: "(action, nat * bool)ioa" where
  "impl_ioa = (impl_sig, {(0,False)}, impl_trans,{},{})"

lemma in_impl_asig:
  "New \<in> actions(impl_sig) \<and>
    Loc l \<in> actions(impl_sig) \<and>
    Free l \<in> actions(impl_sig) "
  by (simp add: impl_sig_def actions_def asig_projections)

end
