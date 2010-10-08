(*  Title:      HOLCF/ex/Domain_Proofs.thy
    Author:     Brian Huffman
*)

header {* Internal domain package proofs done manually *}

theory Domain_Proofs
imports HOLCF
begin

default_sort bifinite

(*

The definitions and proofs below are for the following recursive
datatypes:

domain 'a foo = Foo1 | Foo2 (lazy 'a) (lazy "'a bar")
   and 'a bar = Bar (lazy "'a baz \<rightarrow> tr")
   and 'a baz = Baz (lazy "'a foo convex_pd \<rightarrow> tr")

*)

(********************************************************************)

subsection {* Step 1: Define the new type combinators *}

text {* Start with the one-step non-recursive version *}

definition
  foo_bar_baz_sfpF ::
    "sfp \<rightarrow> sfp \<times> sfp \<times> sfp \<rightarrow> sfp \<times> sfp \<times> sfp"
where
  "foo_bar_baz_sfpF = (\<Lambda> a. Abs_CFun (\<lambda>(t1, t2, t3). 
    ( ssum_sfp\<cdot>SFP(one)\<cdot>(sprod_sfp\<cdot>(u_sfp\<cdot>a)\<cdot>(u_sfp\<cdot>t2))
    , u_sfp\<cdot>(cfun_sfp\<cdot>t3\<cdot>SFP(tr))
    , u_sfp\<cdot>(cfun_sfp\<cdot>(convex_sfp\<cdot>t1)\<cdot>SFP(tr)))))"

lemma foo_bar_baz_sfpF_beta:
  "foo_bar_baz_sfpF\<cdot>a\<cdot>t =
    ( ssum_sfp\<cdot>SFP(one)\<cdot>(sprod_sfp\<cdot>(u_sfp\<cdot>a)\<cdot>(u_sfp\<cdot>(fst (snd t))))
    , u_sfp\<cdot>(cfun_sfp\<cdot>(snd (snd t))\<cdot>SFP(tr))
    , u_sfp\<cdot>(cfun_sfp\<cdot>(convex_sfp\<cdot>(fst t))\<cdot>SFP(tr)))"
unfolding foo_bar_baz_sfpF_def
by (simp add: split_def)

text {* Individual type combinators are projected from the fixed point. *}

definition foo_sfp :: "sfp \<rightarrow> sfp"
where "foo_sfp = (\<Lambda> a. fst (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a)))"

definition bar_sfp :: "sfp \<rightarrow> sfp"
where "bar_sfp = (\<Lambda> a. fst (snd (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a))))"

definition baz_sfp :: "sfp \<rightarrow> sfp"
where "baz_sfp = (\<Lambda> a. snd (snd (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a))))"

lemma defl_apply_thms:
  "foo_sfp\<cdot>a = fst (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a))"
  "bar_sfp\<cdot>a = fst (snd (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a)))"
  "baz_sfp\<cdot>a = snd (snd (fix\<cdot>(foo_bar_baz_sfpF\<cdot>a)))"
unfolding foo_sfp_def bar_sfp_def baz_sfp_def by simp_all

text {* Unfold rules for each combinator. *}

lemma foo_sfp_unfold:
  "foo_sfp\<cdot>a = ssum_sfp\<cdot>SFP(one)\<cdot>(sprod_sfp\<cdot>(u_sfp\<cdot>a)\<cdot>(u_sfp\<cdot>(bar_sfp\<cdot>a)))"
unfolding defl_apply_thms by (subst fix_eq, simp add: foo_bar_baz_sfpF_beta)

lemma bar_sfp_unfold: "bar_sfp\<cdot>a = u_sfp\<cdot>(cfun_sfp\<cdot>(baz_sfp\<cdot>a)\<cdot>SFP(tr))"
unfolding defl_apply_thms by (subst fix_eq, simp add: foo_bar_baz_sfpF_beta)

lemma baz_sfp_unfold: "baz_sfp\<cdot>a = u_sfp\<cdot>(cfun_sfp\<cdot>(convex_sfp\<cdot>(foo_sfp\<cdot>a))\<cdot>SFP(tr))"
unfolding defl_apply_thms by (subst fix_eq, simp add: foo_bar_baz_sfpF_beta)

text "The automation for the previous steps will be quite similar to
how the fixrec package works."

(********************************************************************)

subsection {* Step 2: Define types, prove class instances *}

text {* Use @{text pcpodef} with the appropriate type combinator. *}

pcpodef (open) 'a foo = "{x. x ::: foo_sfp\<cdot>SFP('a)}"
by (simp_all add: adm_in_sfp)

pcpodef (open) 'a bar = "{x. x ::: bar_sfp\<cdot>SFP('a)}"
by (simp_all add: adm_in_sfp)

pcpodef (open) 'a baz = "{x. x ::: baz_sfp\<cdot>SFP('a)}"
by (simp_all add: adm_in_sfp)

text {* Prove rep instance using lemma @{text typedef_rep_class}. *}

instantiation foo :: (bifinite) bifinite
begin

definition emb_foo :: "'a foo \<rightarrow> udom"
where "emb_foo \<equiv> (\<Lambda> x. Rep_foo x)"

definition prj_foo :: "udom \<rightarrow> 'a foo"
where "prj_foo \<equiv> (\<Lambda> y. Abs_foo (cast\<cdot>(foo_sfp\<cdot>SFP('a))\<cdot>y))"

definition sfp_foo :: "'a foo itself \<Rightarrow> sfp"
where "sfp_foo \<equiv> \<lambda>a. foo_sfp\<cdot>SFP('a)"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_foo)
apply (rule below_foo_def)
apply (rule emb_foo_def)
apply (rule prj_foo_def)
apply (rule sfp_foo_def)
done

end

instantiation bar :: (bifinite) bifinite
begin

definition emb_bar :: "'a bar \<rightarrow> udom"
where "emb_bar \<equiv> (\<Lambda> x. Rep_bar x)"

definition prj_bar :: "udom \<rightarrow> 'a bar"
where "prj_bar \<equiv> (\<Lambda> y. Abs_bar (cast\<cdot>(bar_sfp\<cdot>SFP('a))\<cdot>y))"

definition sfp_bar :: "'a bar itself \<Rightarrow> sfp"
where "sfp_bar \<equiv> \<lambda>a. bar_sfp\<cdot>SFP('a)"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_bar)
apply (rule below_bar_def)
apply (rule emb_bar_def)
apply (rule prj_bar_def)
apply (rule sfp_bar_def)
done

end

instantiation baz :: (bifinite) bifinite
begin

definition emb_baz :: "'a baz \<rightarrow> udom"
where "emb_baz \<equiv> (\<Lambda> x. Rep_baz x)"

definition prj_baz :: "udom \<rightarrow> 'a baz"
where "prj_baz \<equiv> (\<Lambda> y. Abs_baz (cast\<cdot>(baz_sfp\<cdot>SFP('a))\<cdot>y))"

definition sfp_baz :: "'a baz itself \<Rightarrow> sfp"
where "sfp_baz \<equiv> \<lambda>a. baz_sfp\<cdot>SFP('a)"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_baz)
apply (rule below_baz_def)
apply (rule emb_baz_def)
apply (rule prj_baz_def)
apply (rule sfp_baz_def)
done

end

text {* Prove SFP rules using lemma @{text typedef_SFP}. *}

lemma SFP_foo: "SFP('a foo) = foo_sfp\<cdot>SFP('a)"
apply (rule typedef_SFP)
apply (rule sfp_foo_def)
done

lemma SFP_bar: "SFP('a bar) = bar_sfp\<cdot>SFP('a)"
apply (rule typedef_SFP)
apply (rule sfp_bar_def)
done

lemma SFP_baz: "SFP('a baz) = baz_sfp\<cdot>SFP('a)"
apply (rule typedef_SFP)
apply (rule sfp_baz_def)
done

text {* Prove SFP equations using type combinator unfold lemmas. *}

lemmas SFP_simps =
  SFP_ssum SFP_sprod SFP_u SFP_cfun

lemma SFP_foo': "SFP('a foo) = SFP(one \<oplus> 'a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>)"
unfolding SFP_foo SFP_bar SFP_baz SFP_simps
by (rule foo_sfp_unfold)

lemma SFP_bar': "SFP('a bar) = SFP(('a baz \<rightarrow> tr)\<^sub>\<bottom>)"
unfolding SFP_foo SFP_bar SFP_baz SFP_simps
by (rule bar_sfp_unfold)

lemma SFP_baz': "SFP('a baz) = SFP(('a foo convex_pd \<rightarrow> tr)\<^sub>\<bottom>)"
unfolding SFP_foo SFP_bar SFP_baz SFP_simps SFP_convex
by (rule baz_sfp_unfold)

(********************************************************************)

subsection {* Step 3: Define rep and abs functions *}

text {* Define them all using @{text coerce}! *}

definition foo_rep :: "'a foo \<rightarrow> one \<oplus> ('a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>)"
where "foo_rep \<equiv> coerce"

definition foo_abs :: "one \<oplus> ('a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>) \<rightarrow> 'a foo"
where "foo_abs \<equiv> coerce"

definition bar_rep :: "'a bar \<rightarrow> ('a baz \<rightarrow> tr)\<^sub>\<bottom>"
where "bar_rep \<equiv> coerce"

definition bar_abs :: "('a baz \<rightarrow> tr)\<^sub>\<bottom> \<rightarrow> 'a bar"
where "bar_abs \<equiv> coerce"

definition baz_rep :: "'a baz \<rightarrow> ('a foo convex_pd \<rightarrow> tr)\<^sub>\<bottom>"
where "baz_rep \<equiv> coerce"

definition baz_abs :: "('a foo convex_pd \<rightarrow> tr)\<^sub>\<bottom> \<rightarrow> 'a baz"
where "baz_abs \<equiv> coerce"

text {* Prove isomorphism rules. *}

lemma foo_abs_iso: "foo_rep\<cdot>(foo_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF SFP_foo' foo_abs_def foo_rep_def])

lemma foo_rep_iso: "foo_abs\<cdot>(foo_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF SFP_foo' foo_abs_def foo_rep_def])

lemma bar_abs_iso: "bar_rep\<cdot>(bar_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF SFP_bar' bar_abs_def bar_rep_def])

lemma bar_rep_iso: "bar_abs\<cdot>(bar_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF SFP_bar' bar_abs_def bar_rep_def])

lemma baz_abs_iso: "baz_rep\<cdot>(baz_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF SFP_baz' baz_abs_def baz_rep_def])

lemma baz_rep_iso: "baz_abs\<cdot>(baz_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF SFP_baz' baz_abs_def baz_rep_def])

text {* Prove isodefl rules using @{text isodefl_coerce}. *}

lemma isodefl_foo_abs:
  "isodefl d t \<Longrightarrow> isodefl (foo_abs oo d oo foo_rep) t"
by (rule isodefl_abs_rep [OF SFP_foo' foo_abs_def foo_rep_def])

lemma isodefl_bar_abs:
  "isodefl d t \<Longrightarrow> isodefl (bar_abs oo d oo bar_rep) t"
by (rule isodefl_abs_rep [OF SFP_bar' bar_abs_def bar_rep_def])

lemma isodefl_baz_abs:
  "isodefl d t \<Longrightarrow> isodefl (baz_abs oo d oo baz_rep) t"
by (rule isodefl_abs_rep [OF SFP_baz' baz_abs_def baz_rep_def])

(********************************************************************)

subsection {* Step 4: Define map functions, prove isodefl property *}

text {* Start with the one-step non-recursive version. *}

text {* Note that the type of the map function depends on which
variables are used in positive and negative positions. *}

definition
  foo_bar_baz_mapF ::
    "('a \<rightarrow> 'b) \<rightarrow>
     ('a foo \<rightarrow> 'b foo) \<times> ('a bar \<rightarrow> 'b bar) \<times> ('b baz \<rightarrow> 'a baz) \<rightarrow>
     ('a foo \<rightarrow> 'b foo) \<times> ('a bar \<rightarrow> 'b bar) \<times> ('b baz \<rightarrow> 'a baz)"
where
  "foo_bar_baz_mapF = (\<Lambda> f. Abs_CFun (\<lambda>(d1, d2, d3).
    (
      foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>d2))
          oo foo_rep
    ,
      bar_abs oo u_map\<cdot>(cfun_map\<cdot>d3\<cdot>ID) oo bar_rep
    ,
      baz_abs oo u_map\<cdot>(cfun_map\<cdot>(convex_map\<cdot>d1)\<cdot>ID) oo baz_rep
    )))"

lemma foo_bar_baz_mapF_beta:
  "foo_bar_baz_mapF\<cdot>f\<cdot>d =
    (
      foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>(fst (snd d))))
          oo foo_rep
    ,
      bar_abs oo u_map\<cdot>(cfun_map\<cdot>(snd (snd d))\<cdot>ID) oo bar_rep
    ,
      baz_abs oo u_map\<cdot>(cfun_map\<cdot>(convex_map\<cdot>(fst d))\<cdot>ID) oo baz_rep
    )"
unfolding foo_bar_baz_mapF_def
by (simp add: split_def)

text {* Individual map functions are projected from the fixed point. *}

definition foo_map :: "('a \<rightarrow> 'b) \<rightarrow> ('a foo \<rightarrow> 'b foo)"
where "foo_map = (\<Lambda> f. fst (fix\<cdot>(foo_bar_baz_mapF\<cdot>f)))"

definition bar_map :: "('a \<rightarrow> 'b) \<rightarrow> ('a bar \<rightarrow> 'b bar)"
where "bar_map = (\<Lambda> f. fst (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f))))"

definition baz_map :: "('a \<rightarrow> 'b) \<rightarrow> ('b baz \<rightarrow> 'a baz)"
where "baz_map = (\<Lambda> f. snd (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f))))"

lemma map_apply_thms:
  "foo_map\<cdot>f = fst (fix\<cdot>(foo_bar_baz_mapF\<cdot>f))"
  "bar_map\<cdot>f = fst (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f)))"
  "baz_map\<cdot>f = snd (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f)))"
unfolding foo_map_def bar_map_def baz_map_def by simp_all

text {* Prove isodefl rules for all map functions simultaneously. *}

lemma isodefl_foo_bar_baz:
  assumes isodefl_d: "isodefl d t"
  shows
  "isodefl (foo_map\<cdot>d) (foo_sfp\<cdot>t) \<and>
  isodefl (bar_map\<cdot>d) (bar_sfp\<cdot>t) \<and>
  isodefl (baz_map\<cdot>d) (baz_sfp\<cdot>t)"
unfolding map_apply_thms defl_apply_thms
 apply (rule parallel_fix_ind)
   apply (intro adm_conj adm_isodefl cont2cont_fst cont2cont_snd cont_id)
  apply (simp only: fst_strict snd_strict isodefl_bottom simp_thms)
 apply (simp only: foo_bar_baz_mapF_beta
                   foo_bar_baz_sfpF_beta
                   fst_conv snd_conv)
 apply (elim conjE)
 apply (intro
  conjI
  isodefl_foo_abs
  isodefl_bar_abs
  isodefl_baz_abs
  isodefl_ssum isodefl_sprod isodefl_ID_SFP
  isodefl_u isodefl_convex isodefl_cfun
  isodefl_d
 )
 apply assumption+
done

lemmas isodefl_foo = isodefl_foo_bar_baz [THEN conjunct1]
lemmas isodefl_bar = isodefl_foo_bar_baz [THEN conjunct2, THEN conjunct1]
lemmas isodefl_baz = isodefl_foo_bar_baz [THEN conjunct2, THEN conjunct2]

text {* Prove map ID lemmas, using isodefl_SFP_imp_ID *}

lemma foo_map_ID: "foo_map\<cdot>ID = ID"
apply (rule isodefl_SFP_imp_ID)
apply (subst SFP_foo)
apply (rule isodefl_foo)
apply (rule isodefl_ID_SFP)
done

lemma bar_map_ID: "bar_map\<cdot>ID = ID"
apply (rule isodefl_SFP_imp_ID)
apply (subst SFP_bar)
apply (rule isodefl_bar)
apply (rule isodefl_ID_SFP)
done

lemma baz_map_ID: "baz_map\<cdot>ID = ID"
apply (rule isodefl_SFP_imp_ID)
apply (subst SFP_baz)
apply (rule isodefl_baz)
apply (rule isodefl_ID_SFP)
done

(********************************************************************)

subsection {* Step 5: Define take functions, prove lub-take lemmas *}

definition
  foo_bar_baz_takeF ::
    "('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz) \<rightarrow>
     ('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz)"
where
  "foo_bar_baz_takeF = (\<Lambda> p.
    ( foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>(fst (snd p))))
          oo foo_rep
    , bar_abs oo
        u_map\<cdot>(cfun_map\<cdot>(snd (snd p))\<cdot>ID) oo bar_rep
    , baz_abs oo
        u_map\<cdot>(cfun_map\<cdot>(convex_map\<cdot>(fst p))\<cdot>ID) oo baz_rep
    ))"

lemma foo_bar_baz_takeF_beta:
  "foo_bar_baz_takeF\<cdot>p =
    ( foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>(fst (snd p))))
          oo foo_rep
    , bar_abs oo
        u_map\<cdot>(cfun_map\<cdot>(snd (snd p))\<cdot>ID) oo bar_rep
    , baz_abs oo
        u_map\<cdot>(cfun_map\<cdot>(convex_map\<cdot>(fst p))\<cdot>ID) oo baz_rep
    )"
unfolding foo_bar_baz_takeF_def by (rule beta_cfun, simp)

definition
  foo_take :: "nat \<Rightarrow> 'a foo \<rightarrow> 'a foo"
where
  "foo_take = (\<lambda>n. fst (iterate n\<cdot>foo_bar_baz_takeF\<cdot>\<bottom>))"

definition
  bar_take :: "nat \<Rightarrow> 'a bar \<rightarrow> 'a bar"
where
  "bar_take = (\<lambda>n. fst (snd (iterate n\<cdot>foo_bar_baz_takeF\<cdot>\<bottom>)))"

definition
  baz_take :: "nat \<Rightarrow> 'a baz \<rightarrow> 'a baz"
where
  "baz_take = (\<lambda>n. snd (snd (iterate n\<cdot>foo_bar_baz_takeF\<cdot>\<bottom>)))"

lemma chain_take_thms: "chain foo_take" "chain bar_take" "chain baz_take"
unfolding foo_take_def bar_take_def baz_take_def
by (intro ch2ch_fst ch2ch_snd chain_iterate)+

lemma take_0_thms: "foo_take 0 = \<bottom>" "bar_take 0 = \<bottom>" "baz_take 0 = \<bottom>"
unfolding foo_take_def bar_take_def baz_take_def
by (simp only: iterate_0 fst_strict snd_strict)+

lemma take_Suc_thms:
  "foo_take (Suc n) =
    foo_abs oo ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>(bar_take n))) oo foo_rep"
  "bar_take (Suc n) =
    bar_abs oo u_map\<cdot>(cfun_map\<cdot>(baz_take n)\<cdot>ID) oo bar_rep"
  "baz_take (Suc n) =
    baz_abs oo u_map\<cdot>(cfun_map\<cdot>(convex_map\<cdot>(foo_take n))\<cdot>ID) oo baz_rep"
unfolding foo_take_def bar_take_def baz_take_def
by (simp only: iterate_Suc foo_bar_baz_takeF_beta fst_conv snd_conv)+

lemma lub_take_lemma:
  "(\<Squnion>n. foo_take n, \<Squnion>n. bar_take n, \<Squnion>n. baz_take n)
    = (foo_map\<cdot>(ID::'a \<rightarrow> 'a), bar_map\<cdot>(ID::'a \<rightarrow> 'a), baz_map\<cdot>(ID::'a \<rightarrow> 'a))"
apply (simp only: thelub_Pair [symmetric] ch2ch_Pair chain_take_thms)
apply (simp only: map_apply_thms pair_collapse)
apply (simp only: fix_def2)
apply (rule lub_eq)
apply (rule nat.induct)
apply (simp only: iterate_0 Pair_strict take_0_thms)
apply (simp only: iterate_Suc Pair_fst_snd_eq fst_conv snd_conv
                  foo_bar_baz_mapF_beta take_Suc_thms simp_thms)
done

lemma lub_foo_take: "(\<Squnion>n. foo_take n) = ID"
apply (rule trans [OF _ foo_map_ID])
using lub_take_lemma
apply (elim Pair_inject)
apply assumption
done

lemma lub_bar_take: "(\<Squnion>n. bar_take n) = ID"
apply (rule trans [OF _ bar_map_ID])
using lub_take_lemma
apply (elim Pair_inject)
apply assumption
done

lemma lub_baz_take: "(\<Squnion>n. baz_take n) = ID"
apply (rule trans [OF _ baz_map_ID])
using lub_take_lemma
apply (elim Pair_inject)
apply assumption
done

end
