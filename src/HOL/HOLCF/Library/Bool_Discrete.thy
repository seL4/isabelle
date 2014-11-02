(*  Title:      HOL/HOLCF/Library/Bool_Discrete.thy
    Author:     Brian Huffman
*)

section {* Discrete cpo instance for booleans *}

theory Bool_Discrete
imports HOLCF
begin

text {* Discrete cpo instance for @{typ bool}. *}

instantiation bool :: discrete_cpo
begin

definition below_bool_def:
  "(x::bool) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_bool_def)

end

text {*
  TODO: implement a command to automate discrete predomain instances.
*}

instantiation bool :: predomain
begin

definition
  "(liftemb :: bool u \<rightarrow> udom u) \<equiv> liftemb oo u_map\<cdot>(\<Lambda> x. Discr x)"

definition
  "(liftprj :: udom u \<rightarrow> bool u) \<equiv> u_map\<cdot>(\<Lambda> y. undiscr y) oo liftprj"

definition
  "liftdefl \<equiv> (\<lambda>(t::bool itself). LIFTDEFL(bool discr))"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> bool u)"
    unfolding liftemb_bool_def liftprj_bool_def
    apply (rule ep_pair_comp)
    apply (rule ep_pair_u_map)
    apply (simp add: ep_pair.intro)
    apply (rule predomain_ep)
    done
  show "cast\<cdot>LIFTDEFL(bool) = liftemb oo (liftprj :: udom u \<rightarrow> bool u)"
    unfolding liftemb_bool_def liftprj_bool_def liftdefl_bool_def
    apply (simp add: cast_liftdefl cfcomp1 u_map_map)
    apply (simp add: ID_def [symmetric] u_map_ID)
    done
qed

end

lemma cont2cont_if [simp, cont2cont]:
  assumes b: "cont b" and f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. if b x then f x else g x)"
by (rule cont_apply [OF b cont_discrete_cpo], simp add: f g)

lemma cont2cont_eq [simp, cont2cont]:
  fixes f g :: "'a::cpo \<Rightarrow> 'b::discrete_cpo"
  assumes f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. f x = g x)"
apply (rule cont_apply [OF f cont_discrete_cpo])
apply (rule cont_apply [OF g cont_discrete_cpo])
apply (rule cont_const)
done

end
