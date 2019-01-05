(*  Title:      HOL/HOLCF/Library/Char_Discrete.thy
    Author:     Brian Huffman
*)

section \<open>Discrete cpo instance for 8-bit char type\<close>

theory Char_Discrete
imports HOLCF
begin

subsection \<open>Discrete cpo instance for \<^typ>\<open>char\<close>.\<close>

instantiation char :: discrete_cpo
begin

definition below_char_def:
  "(x::char) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_char_def)

end

text \<open>
  TODO: implement a command to automate discrete predomain instances.
\<close>

instantiation char :: predomain
begin

definition
  "(liftemb :: char u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> char u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::char itself). LIFTDEFL(char discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> char u)"
    unfolding liftemb_char_def liftprj_char_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(char) = liftemb oo (liftprj :: udom u \<rightarrow> char u)"
    unfolding liftemb_char_def liftprj_char_def liftdefl_char_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

end
