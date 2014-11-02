(*  Title:      HOL/HOLCF/Library/Nat_Discrete.thy
    Author:     Brian Huffman
*)

section {* Discrete cpo instance for naturals *}

theory Nat_Discrete
imports HOLCF
begin

text {* Discrete cpo instance for @{typ nat}. *}

instantiation nat :: discrete_cpo
begin

definition below_nat_def:
  "(x::nat) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_nat_def)

end

text {*
  TODO: implement a command to automate discrete predomain instances.
*}

instantiation nat :: predomain
begin

definition
  "(liftemb :: nat u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> nat u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::nat itself). LIFTDEFL(nat discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> nat u)"
    unfolding liftemb_nat_def liftprj_nat_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(nat) = liftemb oo (liftprj :: udom u \<rightarrow> nat u)"
    unfolding liftemb_nat_def liftprj_nat_def liftdefl_nat_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

end
