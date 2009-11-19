(*  Title:      HOLCF/ex/Domain_Proofs.thy
    Author:     Brian Huffman
*)

header {* Internal domain package proofs done manually *}

theory Domain_Proofs
imports HOLCF
begin

defaultsort rep

(*

The definitions and proofs below are for the following recursive
datatypes:

domain 'a foo = Foo1 | Foo2 (lazy 'a) (lazy "'a bar")
   and 'a bar = Bar (lazy 'a) (lazy "'a baz")
   and 'a baz = Baz (lazy 'a) (lazy "'a foo convex_pd")

*)

(********************************************************************)

subsection {* Step 1: Define the new type combinators *}

text {* Start with the one-step non-recursive version *}

definition
  foo_bar_baz_typF ::
    "TypeRep \<rightarrow> TypeRep \<times> TypeRep \<times> TypeRep \<rightarrow> TypeRep \<times> TypeRep \<times> TypeRep"
where
  "foo_bar_baz_typF = (\<Lambda> a. Abs_CFun (\<lambda>(t1, t2, t3). 
    ( ssum_typ\<cdot>REP(one)\<cdot>(sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>t2))
    , sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>t3)
    , sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(convex_typ\<cdot>t1)))))"

lemma foo_bar_baz_typF_beta:
  "foo_bar_baz_typF\<cdot>a\<cdot>t =
    ( ssum_typ\<cdot>REP(one)\<cdot>(sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(fst (snd t))))
    , sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(snd (snd t)))
    , sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(convex_typ\<cdot>(fst t))))"
unfolding foo_bar_baz_typF_def
by (simp add: split_def)

text {* Individual type combinators are projected from the fixed point. *}

definition foo_typ :: "TypeRep \<rightarrow> TypeRep"
where "foo_typ = (\<Lambda> a. fst (fix\<cdot>(foo_bar_baz_typF\<cdot>a)))"

definition bar_typ :: "TypeRep \<rightarrow> TypeRep"
where "bar_typ = (\<Lambda> a. fst (snd (fix\<cdot>(foo_bar_baz_typF\<cdot>a))))"

definition baz_typ :: "TypeRep \<rightarrow> TypeRep"
where "baz_typ = (\<Lambda> a. snd (snd (fix\<cdot>(foo_bar_baz_typF\<cdot>a))))"

text {* Unfold rules for each combinator. *}

lemma foo_typ_unfold:
  "foo_typ\<cdot>a = ssum_typ\<cdot>REP(one)\<cdot>(sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(bar_typ\<cdot>a)))"
unfolding foo_typ_def bar_typ_def baz_typ_def
by (subst fix_eq, simp add: foo_bar_baz_typF_beta)

lemma bar_typ_unfold: "bar_typ\<cdot>a = sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(baz_typ\<cdot>a))"
unfolding foo_typ_def bar_typ_def baz_typ_def
by (subst fix_eq, simp add: foo_bar_baz_typF_beta)

lemma baz_typ_unfold: "baz_typ\<cdot>a = sprod_typ\<cdot>(u_typ\<cdot>a)\<cdot>(u_typ\<cdot>(convex_typ\<cdot>(foo_typ\<cdot>a)))"
unfolding foo_typ_def bar_typ_def baz_typ_def
by (subst fix_eq, simp add: foo_bar_baz_typF_beta)

text "The automation for the previous steps will be quite similar to
how the fixrec package works."

(********************************************************************)

subsection {* Step 2: Define types, prove class instances *}

text {* Use @{text pcpodef} with the appropriate type combinator. *}

pcpodef (open) 'a foo = "{x. x ::: foo_typ\<cdot>REP('a)}"
by (simp_all add: adm_in_deflation)

pcpodef (open) 'a bar = "{x. x ::: bar_typ\<cdot>REP('a)}"
by (simp_all add: adm_in_deflation)

pcpodef (open) 'a baz = "{x. x ::: baz_typ\<cdot>REP('a)}"
by (simp_all add: adm_in_deflation)

text {* Prove rep instance using lemma @{text typedef_rep_class}. *}

instantiation foo :: (rep) rep
begin

definition emb_foo :: "'a foo \<rightarrow> udom"
where "emb_foo \<equiv> (\<Lambda> x. Rep_foo x)"

definition prj_foo :: "udom \<rightarrow> 'a foo"
where "prj_foo \<equiv> (\<Lambda> y. Abs_foo (cast\<cdot>(foo_typ\<cdot>REP('a))\<cdot>y))"

definition approx_foo :: "nat \<Rightarrow> 'a foo \<rightarrow> 'a foo"
where "approx_foo \<equiv> repdef_approx Rep_foo Abs_foo (foo_typ\<cdot>REP('a))"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_foo)
apply (rule below_foo_def)
apply (rule emb_foo_def)
apply (rule prj_foo_def)
apply (rule approx_foo_def)
done

end

instantiation bar :: (rep) rep
begin

definition emb_bar :: "'a bar \<rightarrow> udom"
where "emb_bar \<equiv> (\<Lambda> x. Rep_bar x)"

definition prj_bar :: "udom \<rightarrow> 'a bar"
where "prj_bar \<equiv> (\<Lambda> y. Abs_bar (cast\<cdot>(bar_typ\<cdot>REP('a))\<cdot>y))"

definition approx_bar :: "nat \<Rightarrow> 'a bar \<rightarrow> 'a bar"
where "approx_bar \<equiv> repdef_approx Rep_bar Abs_bar (bar_typ\<cdot>REP('a))"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_bar)
apply (rule below_bar_def)
apply (rule emb_bar_def)
apply (rule prj_bar_def)
apply (rule approx_bar_def)
done

end

instantiation baz :: (rep) rep
begin

definition emb_baz :: "'a baz \<rightarrow> udom"
where "emb_baz \<equiv> (\<Lambda> x. Rep_baz x)"

definition prj_baz :: "udom \<rightarrow> 'a baz"
where "prj_baz \<equiv> (\<Lambda> y. Abs_baz (cast\<cdot>(baz_typ\<cdot>REP('a))\<cdot>y))"

definition approx_baz :: "nat \<Rightarrow> 'a baz \<rightarrow> 'a baz"
where "approx_baz \<equiv> repdef_approx Rep_baz Abs_baz (baz_typ\<cdot>REP('a))"

instance
apply (rule typedef_rep_class)
apply (rule type_definition_baz)
apply (rule below_baz_def)
apply (rule emb_baz_def)
apply (rule prj_baz_def)
apply (rule approx_baz_def)
done

end

text {* Prove REP rules using lemma @{text typedef_REP}. *}

lemma REP_foo: "REP('a foo) = foo_typ\<cdot>REP('a)"
apply (rule typedef_REP)
apply (rule type_definition_foo)
apply (rule below_foo_def)
apply (rule emb_foo_def)
apply (rule prj_foo_def)
done

lemma REP_bar: "REP('a bar) = bar_typ\<cdot>REP('a)"
apply (rule typedef_REP)
apply (rule type_definition_bar)
apply (rule below_bar_def)
apply (rule emb_bar_def)
apply (rule prj_bar_def)
done

lemma REP_baz: "REP('a baz) = baz_typ\<cdot>REP('a)"
apply (rule typedef_REP)
apply (rule type_definition_baz)
apply (rule below_baz_def)
apply (rule emb_baz_def)
apply (rule prj_baz_def)
done

text {* Prove REP equations using type combinator unfold lemmas. *}

lemma REP_foo': "REP('a foo) = REP(one \<oplus> 'a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>)"
unfolding REP_foo REP_bar REP_baz REP_simps
by (rule foo_typ_unfold)

lemma REP_bar': "REP('a bar) = REP('a\<^sub>\<bottom> \<otimes> ('a baz)\<^sub>\<bottom>)"
unfolding REP_foo REP_bar REP_baz REP_simps
by (rule bar_typ_unfold)

lemma REP_baz': "REP('a baz) = REP('a\<^sub>\<bottom> \<otimes> ('a foo convex_pd)\<^sub>\<bottom>)"
unfolding REP_foo REP_bar REP_baz REP_simps
by (rule baz_typ_unfold)

(********************************************************************)

subsection {* Step 3: Define rep and abs functions *}

text {* Define them all using @{text coerce}! *}

definition foo_rep :: "'a foo \<rightarrow> one \<oplus> ('a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>)"
where "foo_rep \<equiv> coerce"

definition foo_abs :: "one \<oplus> ('a\<^sub>\<bottom> \<otimes> ('a bar)\<^sub>\<bottom>) \<rightarrow> 'a foo"
where "foo_abs \<equiv> coerce"

definition bar_rep :: "'a bar \<rightarrow> 'a\<^sub>\<bottom> \<otimes> ('a baz)\<^sub>\<bottom>"
where "bar_rep \<equiv> coerce"

definition bar_abs :: "'a\<^sub>\<bottom> \<otimes> ('a baz)\<^sub>\<bottom> \<rightarrow> 'a bar"
where "bar_abs \<equiv> coerce"

definition baz_rep :: "'a baz \<rightarrow> 'a\<^sub>\<bottom> \<otimes> ('a foo convex_pd)\<^sub>\<bottom>"
where "baz_rep \<equiv> coerce"

definition baz_abs :: "'a\<^sub>\<bottom> \<otimes> ('a foo convex_pd)\<^sub>\<bottom> \<rightarrow> 'a baz"
where "baz_abs \<equiv> coerce"

text {* Prove isomorphism rules. *}

lemma foo_abs_iso: "foo_rep\<cdot>(foo_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF REP_foo' foo_abs_def foo_rep_def])

lemma foo_rep_iso: "foo_abs\<cdot>(foo_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF REP_foo' foo_abs_def foo_rep_def])

lemma bar_abs_iso: "bar_rep\<cdot>(bar_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF REP_bar' bar_abs_def bar_rep_def])

lemma bar_rep_iso: "bar_abs\<cdot>(bar_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF REP_bar' bar_abs_def bar_rep_def])

lemma baz_abs_iso: "baz_rep\<cdot>(baz_abs\<cdot>x) = x"
by (rule domain_abs_iso [OF REP_baz' baz_abs_def baz_rep_def])

lemma baz_rep_iso: "baz_abs\<cdot>(baz_rep\<cdot>x) = x"
by (rule domain_rep_iso [OF REP_baz' baz_abs_def baz_rep_def])

text {* Prove isodefl rules using @{text isodefl_coerce}. *}

lemma isodefl_foo_abs:
  "isodefl d t \<Longrightarrow> isodefl (foo_abs oo d oo foo_rep) t"
by (rule isodefl_abs_rep [OF REP_foo' foo_abs_def foo_rep_def])

lemma isodefl_bar_abs:
  "isodefl d t \<Longrightarrow> isodefl (bar_abs oo d oo bar_rep) t"
by (rule isodefl_abs_rep [OF REP_bar' bar_abs_def bar_rep_def])

lemma isodefl_baz_abs:
  "isodefl d t \<Longrightarrow> isodefl (baz_abs oo d oo baz_rep) t"
by (rule isodefl_abs_rep [OF REP_baz' baz_abs_def baz_rep_def])

(********************************************************************)

subsection {* Step 4: Define map functions, prove isodefl property *}

text {* Start with the one-step non-recursive version. *}

text {* Note that the type of the map function depends on which
variables are used in positive and negative positions. *}

definition
  foo_bar_baz_mapF ::
  "(_ \<rightarrow> _)
     \<rightarrow> (_ foo \<rightarrow> _ foo) \<times> (_ bar \<rightarrow> _ bar) \<times> (_ baz \<rightarrow> _ baz)
     \<rightarrow> (_ foo \<rightarrow> _ foo) \<times> (_ bar \<rightarrow> _ bar) \<times> (_ baz \<rightarrow> _ baz)"
(*
  "('a \<rightarrow> 'b)
     \<rightarrow> ('a foo \<rightarrow> 'b foo) \<times> ('a bar \<rightarrow> 'b bar) \<times> ('a baz \<rightarrow> 'b baz)
     \<rightarrow> ('a foo \<rightarrow> 'b foo) \<times> ('a bar \<rightarrow> 'b bar) \<times> ('a baz \<rightarrow> 'b baz)"
*)
where
  "foo_bar_baz_mapF = (\<Lambda> f. Abs_CFun (\<lambda>(d1, d2, d3).
    (
      foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>d2))
          oo foo_rep
    ,
      bar_abs oo sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>d3) oo bar_rep
    ,
      baz_abs oo sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>(convex_map\<cdot>d1)) oo baz_rep
    )))"

lemma foo_bar_baz_mapF_beta:
  "foo_bar_baz_mapF\<cdot>f\<cdot>d =
    (
      foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>(fst (snd d))))
          oo foo_rep
    ,
      bar_abs oo sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>(snd (snd d))) oo bar_rep
    ,
      baz_abs oo sprod_map\<cdot>(u_map\<cdot>f)\<cdot>(u_map\<cdot>(convex_map\<cdot>(fst d))) oo baz_rep
    )"
unfolding foo_bar_baz_mapF_def
by (simp add: split_def)

text {* Individual map functions are projected from the fixed point. *}

definition foo_map :: "('a \<rightarrow> 'b) \<rightarrow> ('a foo \<rightarrow> 'b foo)"
where "foo_map = (\<Lambda> f. fst (fix\<cdot>(foo_bar_baz_mapF\<cdot>f)))"

definition bar_map :: "('a \<rightarrow> 'b) \<rightarrow> ('a bar \<rightarrow> 'b bar)"
where "bar_map = (\<Lambda> f. fst (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f))))"

definition baz_map :: "('a \<rightarrow> 'b) \<rightarrow> ('a baz \<rightarrow> 'b baz)"
where "baz_map = (\<Lambda> f. snd (snd (fix\<cdot>(foo_bar_baz_mapF\<cdot>f))))"

text {* Prove isodefl rules for all map functions simultaneously. *}

lemma isodefl_foo_bar_baz:
  assumes isodefl_d: "isodefl d t"
  shows
  "isodefl (foo_map\<cdot>d) (foo_typ\<cdot>t) \<and>
  isodefl (bar_map\<cdot>d) (bar_typ\<cdot>t) \<and>
  isodefl (baz_map\<cdot>d) (baz_typ\<cdot>t)"
 apply (simp add: foo_map_def bar_map_def baz_map_def)
 apply (simp add: foo_typ_def bar_typ_def baz_typ_def)
 apply (rule parallel_fix_ind
  [where F="foo_bar_baz_typF\<cdot>t" and G="foo_bar_baz_mapF\<cdot>d"])
   apply (intro adm_conj adm_isodefl cont2cont_fst cont2cont_snd cont_id)
  apply (simp only: fst_strict snd_strict isodefl_bottom simp_thms)
 apply (simp only: foo_bar_baz_mapF_beta
                   foo_bar_baz_typF_beta
                   fst_conv snd_conv)
 apply (elim conjE)
 apply (intro
  conjI
  isodefl_foo_abs
  isodefl_bar_abs
  isodefl_baz_abs
  isodefl_ssum isodefl_sprod isodefl_ID_REP isodefl_u isodefl_convex
  isodefl_d
 )
 apply assumption+
done

lemmas isodefl_foo = isodefl_foo_bar_baz [THEN conjunct1]
lemmas isodefl_bar = isodefl_foo_bar_baz [THEN conjunct2, THEN conjunct1]
lemmas isodefl_baz = isodefl_foo_bar_baz [THEN conjunct2, THEN conjunct2]

text {* Prove map ID lemmas, using isodefl_REP_imp_ID *}

lemma foo_map_ID: "foo_map\<cdot>ID = ID"
apply (rule isodefl_REP_imp_ID)
apply (subst REP_foo)
apply (rule isodefl_foo)
apply (rule isodefl_ID_REP)
done

lemma bar_map_ID: "bar_map\<cdot>ID = ID"
apply (rule isodefl_REP_imp_ID)
apply (subst REP_bar)
apply (rule isodefl_bar)
apply (rule isodefl_ID_REP)
done

lemma baz_map_ID: "baz_map\<cdot>ID = ID"
apply (rule isodefl_REP_imp_ID)
apply (subst REP_baz)
apply (rule isodefl_baz)
apply (rule isodefl_ID_REP)
done

(********************************************************************)

subsection {* Step 5: Define copy functions, prove reach lemmas *}

text {* Define copy functions just like the old domain package does. *}

definition
  foo_copy ::
    "('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz) \<rightarrow>
       'a foo \<rightarrow> 'a foo"
where
  "foo_copy = Abs_CFun (\<lambda>(d1, d2, d3). foo_abs oo
        ssum_map\<cdot>ID\<cdot>(sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>d2))
          oo foo_rep)"

definition
  bar_copy ::
    "('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz) \<rightarrow>
       'a bar \<rightarrow> 'a bar"
where
  "bar_copy = Abs_CFun (\<lambda>(d1, d2, d3). bar_abs oo
        sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>d3) oo bar_rep)"

definition
  baz_copy ::
    "('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz) \<rightarrow>
       'a baz \<rightarrow> 'a baz"
where
  "baz_copy = Abs_CFun (\<lambda>(d1, d2, d3). baz_abs oo
        sprod_map\<cdot>(u_map\<cdot>ID)\<cdot>(u_map\<cdot>(convex_map\<cdot>d1)) oo baz_rep)"

definition
  foo_bar_baz_copy ::
    "('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz) \<rightarrow>
     ('a foo \<rightarrow> 'a foo) \<times> ('a bar \<rightarrow> 'a bar) \<times> ('a baz \<rightarrow> 'a baz)"
where
  "foo_bar_baz_copy = (\<Lambda> f. (foo_copy\<cdot>f, bar_copy\<cdot>f, baz_copy\<cdot>f))"

lemma fix_foo_bar_baz_copy:
  "fix\<cdot>foo_bar_baz_copy = (foo_map\<cdot>ID, bar_map\<cdot>ID, baz_map\<cdot>ID)"
unfolding foo_map_def bar_map_def baz_map_def
apply (subst beta_cfun, simp)+
apply (subst pair_collapse)+
apply (rule cfun_arg_cong)
unfolding foo_bar_baz_copy_def
unfolding foo_copy_def bar_copy_def baz_copy_def
unfolding foo_bar_baz_mapF_def
unfolding split_def
apply (subst beta_cfun, simp)+
apply (rule refl)
done

lemma foo_reach: "fst (fix\<cdot>foo_bar_baz_copy)\<cdot>x = x"
unfolding fix_foo_bar_baz_copy fst_conv snd_conv
unfolding foo_map_ID by (rule ID1)

lemma bar_reach: "fst (snd (fix\<cdot>foo_bar_baz_copy))\<cdot>x = x"
unfolding fix_foo_bar_baz_copy fst_conv snd_conv
unfolding bar_map_ID by (rule ID1)

lemma baz_reach: "snd (snd (fix\<cdot>foo_bar_baz_copy))\<cdot>x = x"
unfolding fix_foo_bar_baz_copy fst_conv snd_conv
unfolding baz_map_ID by (rule ID1)

end
