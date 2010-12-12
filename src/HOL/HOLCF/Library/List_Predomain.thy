(*  Title:      HOLCF/Library/List_Predomain.thy
    Author:     Brian Huffman
*)

header {* Predomain class instance for HOL list type *}

theory List_Predomain
imports List_Cpo
begin

subsection {* Strict list type *}

domain 'a slist = SNil | SCons "'a" "'a slist"

text {*
  Types @{typ "'a list u"}. and @{typ "'a u slist"} are isomorphic.
*}

fixrec encode_list_u where
  "encode_list_u\<cdot>(up\<cdot>[]) = SNil" |
  "encode_list_u\<cdot>(up\<cdot>(x # xs)) = SCons\<cdot>(up\<cdot>x)\<cdot>(encode_list_u\<cdot>(up\<cdot>xs))"

lemma encode_list_u_strict [simp]: "encode_list_u\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma encode_list_u_bottom_iff [simp]:
  "encode_list_u\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
apply (induct x, simp_all)
apply (rename_tac xs, induct_tac xs, simp_all)
done

fixrec decode_list_u where
  "decode_list_u\<cdot>SNil = up\<cdot>[]" |
  "ys \<noteq> \<bottom> \<Longrightarrow> decode_list_u\<cdot>(SCons\<cdot>(up\<cdot>x)\<cdot>ys) =
    (case decode_list_u\<cdot>ys of up\<cdot>xs \<Rightarrow> up\<cdot>(x # xs))"

lemma decode_list_u_strict [simp]: "decode_list_u\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma decode_encode_list_u [simp]: "decode_list_u\<cdot>(encode_list_u\<cdot>x) = x"
by (induct x, simp, rename_tac xs, induct_tac xs, simp_all)

lemma encode_decode_list_u [simp]: "encode_list_u\<cdot>(decode_list_u\<cdot>y) = y"
apply (induct y, simp, simp)
apply (case_tac a, simp)
apply (case_tac "decode_list_u\<cdot>y", simp, simp)
done

subsection {* Lists are a predomain *}

instantiation list :: (predomain) predomain
begin

definition
  "liftemb = emb oo encode_list_u"

definition
  "liftprj = decode_list_u oo prj"

definition
  "liftdefl (t::('a list) itself) = DEFL(('a\<^sub>\<bottom>) slist)"

instance proof
  have "ep_pair encode_list_u decode_list_u"
    by (rule ep_pair.intro, simp_all)
  thus "ep_pair liftemb (liftprj :: udom \<rightarrow> ('a list) u)"
    unfolding liftemb_list_def liftprj_list_def
    using ep_pair_emb_prj by (rule ep_pair_comp)
  show "cast\<cdot>LIFTDEFL('a list) = liftemb oo (liftprj :: udom \<rightarrow> ('a list) u)"
    unfolding liftemb_list_def liftprj_list_def liftdefl_list_def
    by (simp add: cfcomp1 cast_DEFL)
qed

end

lemma liftdefl_list [domain_defl_simps]:
  "LIFTDEFL('a::predomain list) = slist_defl\<cdot>LIFTDEFL('a)"
unfolding liftdefl_list_def by (simp add: domain_defl_simps)

subsection {* Continuous map operation for lists *}

definition
  list_map :: "('a::predomain \<rightarrow> 'b::predomain) \<rightarrow> 'a list \<rightarrow> 'b list"
where
  "list_map = (\<Lambda> f xs. map (\<lambda>x. f\<cdot>x) xs)"

lemma list_map_simps [simp]:
  "list_map\<cdot>f\<cdot>[] = []"
  "list_map\<cdot>f\<cdot>(x # xs) = f\<cdot>x # list_map\<cdot>f\<cdot>xs"
unfolding list_map_def by simp_all

lemma list_map_ID [domain_map_ID]: "list_map\<cdot>ID = ID"
unfolding list_map_def ID_def
by (simp add: Abs_cfun_inverse cfun_def)

lemma deflation_list_map [domain_deflation]:
  "deflation d \<Longrightarrow> deflation (list_map\<cdot>d)"
apply default
apply (induct_tac x, simp_all add: deflation.idem)
apply (induct_tac x, simp_all add: deflation.below)
done

subsection {* Configuring list type to work with domain package *}

lemma encode_list_u_map:
  "encode_list_u\<cdot>(u_map\<cdot>(list_map\<cdot>f)\<cdot>(decode_list_u\<cdot>xs))
    = slist_map\<cdot>(u_map\<cdot>f)\<cdot>xs"
apply (induct xs)
apply (simp, subst slist_map_unfold, simp)
apply (simp, subst slist_map_unfold, simp add: SNil_def)
apply (case_tac a, simp, rename_tac b)
apply (case_tac "decode_list_u\<cdot>xs")
apply (drule_tac f="encode_list_u" in cfun_arg_cong, simp)
by (simp, subst slist_map_unfold, simp add: SCons_def)

lemma isodefl_list_u [domain_isodefl]:
  fixes d :: "'a::predomain \<rightarrow> 'a"
  assumes "isodefl (u_map\<cdot>d) t"
  shows "isodefl (u_map\<cdot>(list_map\<cdot>d)) (slist_defl\<cdot>t)"
using assms [THEN isodefl_slist] unfolding isodefl_def
unfolding emb_u_def prj_u_def liftemb_list_def liftprj_list_def
by (simp add: cfcomp1 encode_list_u_map)

setup {*
  Domain_Take_Proofs.add_rec_type (@{type_name "list"}, [true])
*}

end
