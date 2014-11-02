(*  Title:      HOL/HOLCF/Library/List_Predomain.thy
    Author:     Brian Huffman
*)

section {* Predomain class instance for HOL list type *}

theory List_Predomain
imports List_Cpo Sum_Cpo
begin

subsection {* Strict list type *}

domain 'a slist = SNil | SCons "'a" "'a slist"

text {* Polymorphic map function for strict lists. *}

text {* FIXME: The domain package should generate this! *}

fixrec slist_map' :: "('a \<rightarrow> 'b) \<rightarrow> 'a slist \<rightarrow> 'b slist"
  where "slist_map'\<cdot>f\<cdot>SNil = SNil"
  | "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow>
      slist_map'\<cdot>f\<cdot>(SCons\<cdot>x\<cdot>xs) = SCons\<cdot>(f\<cdot>x)\<cdot>(slist_map'\<cdot>f\<cdot>xs)"

lemma slist_map'_strict [simp]: "slist_map'\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma slist_map_conv [simp]: "slist_map = slist_map'"
apply (rule cfun_eqI, rule cfun_eqI, rename_tac f xs)
apply (induct_tac xs, simp_all)
apply (subst slist_map_unfold, simp)
apply (subst slist_map_unfold, simp add: SNil_def)
apply (subst slist_map_unfold, simp add: SCons_def)
done

lemma slist_map'_slist_map':
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> slist_map'\<cdot>f\<cdot>(slist_map'\<cdot>g\<cdot>xs) = slist_map'\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
apply (induct xs, simp, simp)
apply (case_tac "g\<cdot>a = \<bottom>", simp, simp)
apply (case_tac "slist_map'\<cdot>g\<cdot>xs = \<bottom>", simp, simp)
done

lemma slist_map'_oo:
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> slist_map'\<cdot>(f oo g) = slist_map'\<cdot>f oo slist_map'\<cdot>g"
by (simp add: cfcomp1 slist_map'_slist_map' eta_cfun)

lemma slist_map'_ID: "slist_map'\<cdot>ID = ID"
by (rule cfun_eqI, induct_tac x, simp_all)

lemma ep_pair_slist_map':
  "ep_pair e p \<Longrightarrow> ep_pair (slist_map'\<cdot>e) (slist_map'\<cdot>p)"
apply (rule ep_pair.intro)
apply (subst slist_map'_slist_map')
apply (erule pcpo_ep_pair.p_strict [unfolded pcpo_ep_pair_def])
apply (simp add: ep_pair.e_inverse ID_def [symmetric] slist_map'_ID)
apply (subst slist_map'_slist_map')
apply (erule pcpo_ep_pair.e_strict [unfolded pcpo_ep_pair_def])
apply (rule below_eq_trans [OF _ ID1])
apply (subst slist_map'_ID [symmetric])
apply (intro monofun_cfun below_refl)
apply (simp add: cfun_below_iff ep_pair.e_p_below)
done

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

definition list_liftdefl :: "udom u defl \<rightarrow> udom u defl"
  where "list_liftdefl = (\<Lambda> a. udefl\<cdot>(slist_defl\<cdot>(u_liftdefl\<cdot>a)))"

lemma cast_slist_defl: "cast\<cdot>(slist_defl\<cdot>a) = emb oo slist_map\<cdot>(cast\<cdot>a) oo prj"
using isodefl_slist [where fa="cast\<cdot>a" and da="a"]
unfolding isodefl_def by simp

instantiation list :: (predomain) predomain
begin

definition
  "liftemb = (strictify\<cdot>up oo emb oo slist_map'\<cdot>u_emb) oo slist_map'\<cdot>liftemb oo encode_list_u"

definition
  "liftprj = (decode_list_u oo slist_map'\<cdot>liftprj) oo (slist_map'\<cdot>u_prj oo prj) oo fup\<cdot>ID"

definition
  "liftdefl (t::('a list) itself) = list_liftdefl\<cdot>LIFTDEFL('a)"

instance proof
  show "ep_pair liftemb (liftprj :: udom u \<rightarrow> ('a list) u)"
    unfolding liftemb_list_def liftprj_list_def
    by (intro ep_pair_comp ep_pair_slist_map' ep_pair_strictify_up
      ep_pair_emb_prj predomain_ep ep_pair_u, simp add: ep_pair.intro)
  show "cast\<cdot>LIFTDEFL('a list) = liftemb oo (liftprj :: udom u \<rightarrow> ('a list) u)"
    unfolding liftemb_list_def liftprj_list_def liftdefl_list_def
    apply (simp add: list_liftdefl_def cast_udefl cast_slist_defl cast_u_liftdefl cast_liftdefl)
    apply (simp add: slist_map'_oo u_emb_bottom cfun_eq_iff)
    done
qed

end

subsection {* Configuring domain package to work with list type *}

lemma liftdefl_list [domain_defl_simps]:
  "LIFTDEFL('a::predomain list) = list_liftdefl\<cdot>LIFTDEFL('a)"
by (rule liftdefl_list_def)

abbreviation list_map :: "('a::cpo \<rightarrow> 'b::cpo) \<Rightarrow> 'a list \<rightarrow> 'b list"
  where "list_map f \<equiv> Abs_cfun (map (Rep_cfun f))"

lemma list_map_ID [domain_map_ID]: "list_map ID = ID"
by (simp add: ID_def)

lemma deflation_list_map [domain_deflation]:
  "deflation d \<Longrightarrow> deflation (list_map d)"
apply default
apply (induct_tac x, simp_all add: deflation.idem)
apply (induct_tac x, simp_all add: deflation.below)
done

lemma encode_list_u_map:
  "encode_list_u\<cdot>(u_map\<cdot>(list_map f)\<cdot>(decode_list_u\<cdot>xs))
    = slist_map\<cdot>(u_map\<cdot>f)\<cdot>xs"
apply (induct xs, simp, simp)
apply (case_tac a, simp, rename_tac b)
apply (case_tac "decode_list_u\<cdot>xs")
apply (drule_tac f="encode_list_u" in cfun_arg_cong, simp, simp)
done

lemma isodefl_list_u [domain_isodefl]:
  fixes d :: "'a::predomain \<rightarrow> 'a"
  assumes "isodefl' d t"
  shows "isodefl' (list_map d) (list_liftdefl\<cdot>t)"
using assms unfolding isodefl'_def liftemb_list_def liftprj_list_def
apply (simp add: list_liftdefl_def cast_udefl cast_slist_defl cast_u_liftdefl)
apply (simp add: cfcomp1 encode_list_u_map)
apply (simp add: slist_map'_slist_map' u_emb_bottom)
done

setup {*
  Domain_Take_Proofs.add_rec_type (@{type_name "list"}, [true])
*}

end
