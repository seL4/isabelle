(*  Title:      HOL/HOLCF/Library/Int_Discrete.thy
    Author:     Brian Huffman
*)

section {* Discrete cpo instance for integers *}

theory Int_Discrete
imports HOLCF
begin

text {* Discrete cpo instance for @{typ int}. *}

instantiation int :: discrete_cpo
begin

definition below_int_def:
  "(x::int) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_int_def)

end

text {*
  TODO: implement a command to automate discrete predomain instances.
*}

instantiation int :: predomain
begin

definition
  "(liftemb :: int u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> int u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::int itself). LIFTDEFL(int discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> int u)"
    unfolding liftemb_int_def liftprj_int_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(int) = liftemb oo (liftprj :: udom u \<rightarrow> int u)"
    unfolding liftemb_int_def liftprj_int_def liftdefl_int_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

end
