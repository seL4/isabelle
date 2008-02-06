(*  Title:      HOLCF/CompactBasis.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Compact bases of domains *}

theory CompactBasis
imports Bifinite SetPcpo
begin

subsection {* Ideals over a preorder *}

locale preorder =
  fixes r :: "'a::type \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "r x x"
  assumes trans: "\<lbrakk>r x y; r y z\<rbrakk> \<Longrightarrow> r x z"
begin

definition
  ideal :: "'a set \<Rightarrow> bool" where
  "ideal A = ((\<exists>x. x \<in> A) \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. r x z \<and> r y z) \<and>
    (\<forall>x y. r x y \<longrightarrow> y \<in> A \<longrightarrow> x \<in> A))"

lemma idealI:
  assumes "\<exists>x. x \<in> A"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. r x z \<and> r y z"
  assumes "\<And>x y. \<lbrakk>r x y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
  shows "ideal A"
unfolding ideal_def using prems by fast

lemma idealD1:
  "ideal A \<Longrightarrow> \<exists>x. x \<in> A"
unfolding ideal_def by fast

lemma idealD2:
  "\<lbrakk>ideal A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. r x z \<and> r y z"
unfolding ideal_def by fast

lemma idealD3:
  "\<lbrakk>ideal A; r x y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
unfolding ideal_def by fast

lemma ideal_directed_finite:
  assumes A: "ideal A"
  shows "\<lbrakk>finite U; U \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. \<forall>x\<in>U. r x z"
apply (induct U set: finite)
apply (simp add: idealD1 [OF A])
apply (simp, clarify, rename_tac y)
apply (drule (1) idealD2 [OF A])
apply (clarify, erule_tac x=z in rev_bexI)
apply (fast intro: trans)
done

lemma ideal_principal: "ideal {x. r x z}"
apply (rule idealI)
apply (rule_tac x=z in exI)
apply (fast intro: refl)
apply (rule_tac x=z in bexI, fast)
apply (fast intro: refl)
apply (fast intro: trans)
done

lemma directed_image_ideal:
  assumes A: "ideal A"
  assumes f: "\<And>x y. r x y \<Longrightarrow> f x \<sqsubseteq> f y"
  shows "directed (f ` A)"
apply (rule directedI)
apply (cut_tac idealD1 [OF A], fast)
apply (clarify, rename_tac a b)
apply (drule (1) idealD2 [OF A])
apply (clarify, rename_tac c)
apply (rule_tac x="f c" in rev_bexI)
apply (erule imageI)
apply (simp add: f)
done

lemma adm_ideal: "adm (\<lambda>A. ideal A)"
unfolding ideal_def by (intro adm_lemmas adm_set_lemmas)

end

subsection {* Defining functions in terms of basis elements *}

lemma (in preorder) lub_image_principal:
  assumes f: "\<And>x y. r x y \<Longrightarrow> f x \<sqsubseteq> f y"
  shows "(\<Squnion>x\<in>{x. r x y}. f x) = f y"
apply (rule thelubI)
apply (rule is_lub_maximal)
apply (rule ub_imageI)
apply (simp add: f)
apply (rule imageI)
apply (simp add: refl)
done

lemma finite_directed_contains_lub:
  "\<lbrakk>finite S; directed S\<rbrakk> \<Longrightarrow> \<exists>u\<in>S. S <<| u"
apply (drule (1) directed_finiteD, rule subset_refl)
apply (erule bexE)
apply (rule rev_bexI, assumption)
apply (erule (1) is_lub_maximal)
done

lemma lub_finite_directed_in_self:
  "\<lbrakk>finite S; directed S\<rbrakk> \<Longrightarrow> lub S \<in> S"
apply (drule (1) finite_directed_contains_lub, clarify)
apply (drule thelubI, simp)
done

lemma finite_directed_has_lub: "\<lbrakk>finite S; directed S\<rbrakk> \<Longrightarrow> \<exists>u. S <<| u"
by (drule (1) finite_directed_contains_lub, fast)

lemma is_ub_thelub0: "\<lbrakk>\<exists>u. S <<| u; x \<in> S\<rbrakk> \<Longrightarrow> x \<sqsubseteq> lub S"
apply (erule exE, drule lubI)
apply (drule is_lubD1)
apply (erule (1) is_ubD)
done

lemma is_lub_thelub0: "\<lbrakk>\<exists>u. S <<| u; S <| x\<rbrakk> \<Longrightarrow> lub S \<sqsubseteq> x"
by (erule exE, drule lubI, erule is_lub_lub)

locale bifinite_basis = preorder +
  fixes principal :: "'a::type \<Rightarrow> 'b::cpo"
  fixes approxes :: "'b::cpo \<Rightarrow> 'a::type set"
  assumes ideal_approxes: "\<And>x. preorder.ideal r (approxes x)"
  assumes cont_approxes: "cont approxes"
  assumes approxes_principal: "\<And>a. approxes (principal a) = {b. r b a}"
  assumes subset_approxesD: "\<And>x y. approxes x \<subseteq> approxes y \<Longrightarrow> x \<sqsubseteq> y"

  fixes take :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'a"
  assumes take_less: "r (take n a) a"
  assumes take_take: "take n (take n a) = take n a"
  assumes take_mono: "r a b \<Longrightarrow> r (take n a) (take n b)"
  assumes take_chain: "r (take n a) (take (Suc n) a)"
  assumes finite_range_take: "finite (range (take n))"
  assumes take_covers: "\<exists>n. take n a = a"
begin

lemma finite_take_approxes: "finite (take n ` approxes x)"
by (rule finite_subset [OF image_mono [OF subset_UNIV] finite_range_take])

lemma basis_fun_lemma0:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "\<exists>u. f ` take i ` approxes x <<| u"
apply (rule finite_directed_has_lub)
apply (rule finite_imageI)
apply (rule finite_take_approxes)
apply (subst image_image)
apply (rule directed_image_ideal)
apply (rule ideal_approxes)
apply (rule f_mono)
apply (erule take_mono)
done

lemma basis_fun_lemma1:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "chain (\<lambda>i. lub (f ` take i ` approxes x))"
 apply (rule chainI)
 apply (rule is_lub_thelub0)
  apply (rule basis_fun_lemma0, erule f_mono)
 apply (rule is_ubI, clarsimp, rename_tac a)
 apply (rule trans_less [OF f_mono [OF take_chain]])
 apply (rule is_ub_thelub0)
  apply (rule basis_fun_lemma0, erule f_mono)
 apply simp
done

lemma basis_fun_lemma2:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "f ` approxes x <<| (\<Squnion>i. lub (f ` take i ` approxes x))"
 apply (rule is_lubI)
 apply (rule ub_imageI, rename_tac a)
  apply (cut_tac a=a in take_covers, erule exE, rename_tac i)
  apply (erule subst)
  apply (rule rev_trans_less)
   apply (rule_tac x=i in is_ub_thelub)
   apply (rule basis_fun_lemma1, erule f_mono)
  apply (rule is_ub_thelub0)
   apply (rule basis_fun_lemma0, erule f_mono)
  apply simp
 apply (rule is_lub_thelub [OF _ ub_rangeI])
  apply (rule basis_fun_lemma1, erule f_mono)
 apply (rule is_lub_thelub0)
  apply (rule basis_fun_lemma0, erule f_mono)
 apply (rule is_ubI, clarsimp, rename_tac a)
 apply (rule trans_less [OF f_mono [OF take_less]])
 apply (erule (1) ub_imageD)
done

lemma basis_fun_lemma:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "\<exists>u. f ` approxes x <<| u"
by (rule exI, rule basis_fun_lemma2, erule f_mono)

lemma approxes_mono: "x \<sqsubseteq> y \<Longrightarrow> approxes x \<subseteq> approxes y"
apply (drule cont_approxes [THEN cont2mono, THEN monofunE])
apply (simp add: set_cpo_simps)
done

lemma approxes_contlub:
  "chain Y \<Longrightarrow> approxes (\<Squnion>i. Y i) = (\<Union>i. approxes (Y i))"
by (simp add: cont2contlubE [OF cont_approxes] set_cpo_simps)

lemma less_def: "(x \<sqsubseteq> y) = (approxes x \<subseteq> approxes y)"
by (rule iffI [OF approxes_mono subset_approxesD])

lemma approxes_eq: "approxes x = {a. principal a \<sqsubseteq> x}"
unfolding less_def approxes_principal
apply safe
apply (erule (1) idealD3 [OF ideal_approxes])
apply (erule subsetD, simp add: refl)
done

lemma mem_approxes_iff: "(a \<in> approxes x) = (principal a \<sqsubseteq> x)"
by (simp add: approxes_eq)

lemma principal_less_iff: "(principal a \<sqsubseteq> x) = (a \<in> approxes x)"
by (simp add: approxes_eq)

lemma approxesD: "a \<in> approxes x \<Longrightarrow> principal a \<sqsubseteq> x"
by (simp add: approxes_eq)

lemma principal_mono: "r a b \<Longrightarrow> principal a \<sqsubseteq> principal b"
by (rule approxesD, simp add: approxes_principal)

lemma lessI: "(\<And>a. principal a \<sqsubseteq> x \<Longrightarrow> principal a \<sqsubseteq> u) \<Longrightarrow> x \<sqsubseteq> u"
unfolding principal_less_iff
by (simp add: less_def subset_def)

lemma lub_principal_approxes: "principal ` approxes x <<| x"
apply (rule is_lubI)
apply (rule ub_imageI)
apply (erule approxesD)
apply (subst less_def)
apply (rule subsetI)
apply (drule (1) ub_imageD)
apply (simp add: approxes_eq)
done

definition
  basis_fun :: "('a::type \<Rightarrow> 'c::cpo) \<Rightarrow> 'b \<rightarrow> 'c" where
  "basis_fun = (\<lambda>f. (\<Lambda> x. lub (f ` approxes x)))"

lemma basis_fun_beta:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>x = lub (f ` approxes x)"
unfolding basis_fun_def
proof (rule beta_cfun)
  have lub: "\<And>x. \<exists>u. f ` approxes x <<| u"
    using f_mono by (rule basis_fun_lemma)
  show cont: "cont (\<lambda>x. lub (f ` approxes x))"
    apply (rule contI2)
     apply (rule monofunI)
     apply (rule is_lub_thelub0 [OF lub ub_imageI])
     apply (rule is_ub_thelub0 [OF lub imageI])
     apply (erule (1) subsetD [OF approxes_mono])
    apply (rule is_lub_thelub0 [OF lub ub_imageI])
    apply (simp add: approxes_contlub, clarify)
    apply (erule rev_trans_less [OF is_ub_thelub])
    apply (erule is_ub_thelub0 [OF lub imageI])
    done
qed

lemma basis_fun_principal:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>(principal a) = f a"
apply (subst basis_fun_beta, erule f_mono)
apply (subst approxes_principal)
apply (rule lub_image_principal, erule f_mono)
done

lemma basis_fun_mono:
  assumes f_mono: "\<And>a b. r a b \<Longrightarrow> f a \<sqsubseteq> f b"
  assumes g_mono: "\<And>a b. r a b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes less: "\<And>a. f a \<sqsubseteq> g a"
  shows "basis_fun f \<sqsubseteq> basis_fun g"
 apply (rule less_cfun_ext)
 apply (simp only: basis_fun_beta f_mono g_mono)
 apply (rule is_lub_thelub0)
  apply (rule basis_fun_lemma, erule f_mono)
 apply (rule ub_imageI, rename_tac a)
 apply (rule trans_less [OF less])
 apply (rule is_ub_thelub0)
  apply (rule basis_fun_lemma, erule g_mono)
 apply (erule imageI)
done

lemma compact_principal: "compact (principal a)"
by (rule compactI2, simp add: principal_less_iff approxes_contlub)

lemma chain_basis_fun_take:
  "chain (\<lambda>i. basis_fun (\<lambda>a. principal (take i a)))"
apply (rule chainI)
apply (rule basis_fun_mono)
apply (erule principal_mono [OF take_mono])
apply (erule principal_mono [OF take_mono])
apply (rule principal_mono [OF take_chain])
done

lemma lub_basis_fun_take:
  "(\<Squnion>i. basis_fun (\<lambda>a. principal (take i a))\<cdot>x) = x"
 apply (simp add: basis_fun_beta principal_mono take_mono)
 apply (subst image_image [where f=principal, symmetric])
 apply (rule unique_lub [OF _ lub_principal_approxes])
 apply (rule basis_fun_lemma2, erule principal_mono)
done

lemma basis_fun_take_eq_principal:
  "\<exists>a\<in>approxes x.
    basis_fun (\<lambda>a. principal (take i a))\<cdot>x = principal (take i a)"
 apply (simp add: basis_fun_beta principal_mono take_mono)
 apply (subst image_image [where f=principal, symmetric])
 apply (subgoal_tac "finite (principal ` take i ` approxes x)")
  apply (subgoal_tac "directed (principal ` take i ` approxes x)")
   apply (drule (1) lub_finite_directed_in_self, fast)
  apply (subst image_image)
  apply (rule directed_image_ideal)
   apply (rule ideal_approxes)
  apply (erule principal_mono [OF take_mono])
 apply (rule finite_imageI)
 apply (rule finite_take_approxes)
done

lemma principal_induct:
  assumes adm: "adm P"
  assumes P: "\<And>a. P (principal a)"
  shows "P x"
 apply (subgoal_tac "P (\<Squnion>i. basis_fun (\<lambda>a. principal (take i a))\<cdot>x)")
 apply (simp add: lub_basis_fun_take)
 apply (rule admD [OF adm])
  apply (simp add: chain_basis_fun_take)
 apply (cut_tac x=x and i=i in basis_fun_take_eq_principal)
 apply (clarify, simp add: P)
done

lemma finite_fixes_basis_fun_take:
  "finite {x. basis_fun (\<lambda>a. principal (take i a))\<cdot>x = x}" (is "finite ?S")
apply (subgoal_tac "?S \<subseteq> principal ` range (take i)")
apply (erule finite_subset)
apply (rule finite_imageI)
apply (rule finite_range_take)
apply (clarify, erule subst)
apply (cut_tac x=x and i=i in basis_fun_take_eq_principal)
apply fast
done

end


subsection {* Compact bases of bifinite domains *}

defaultsort bifinite

typedef (open) 'a compact_basis = "{x::'a::bifinite. compact x}"
by (fast intro: compact_approx)

lemma compact_Rep_compact_basis [simp]: "compact (Rep_compact_basis a)"
by (rule Rep_compact_basis [simplified])

lemma Rep_Abs_compact_basis_approx [simp]:
  "Rep_compact_basis (Abs_compact_basis (approx n\<cdot>x)) = approx n\<cdot>x"
by (rule Abs_compact_basis_inverse, simp)

lemma compact_imp_Rep_compact_basis:
  "compact x \<Longrightarrow> \<exists>y. x = Rep_compact_basis y"
by (rule exI, rule Abs_compact_basis_inverse [symmetric], simp)

definition
  compact_le :: "'a compact_basis \<Rightarrow> 'a compact_basis \<Rightarrow> bool" where
  "compact_le = (\<lambda>x y. Rep_compact_basis x \<sqsubseteq> Rep_compact_basis y)"

lemma compact_le_refl: "compact_le x x"
unfolding compact_le_def by (rule refl_less)

lemma compact_le_trans: "\<lbrakk>compact_le x y; compact_le y z\<rbrakk> \<Longrightarrow> compact_le x z"
unfolding compact_le_def by (rule trans_less)

lemma compact_le_antisym: "\<lbrakk>compact_le x y; compact_le y x\<rbrakk> \<Longrightarrow> x = y"
unfolding compact_le_def
apply (rule Rep_compact_basis_inject [THEN iffD1])
apply (erule (1) antisym_less)
done

interpretation compact_le: preorder [compact_le]
by (rule preorder.intro, rule compact_le_refl, rule compact_le_trans)

text {* minimal compact element *}

definition
  compact_bot :: "'a compact_basis" where
  "compact_bot = Abs_compact_basis \<bottom>"

lemma Rep_compact_bot: "Rep_compact_basis compact_bot = \<bottom>"
unfolding compact_bot_def by (simp add: Abs_compact_basis_inverse)

lemma compact_minimal [simp]: "compact_le compact_bot a"
unfolding compact_le_def Rep_compact_bot by simp

text {* compacts *}

definition
  compacts :: "'a \<Rightarrow> 'a compact_basis set" where
  "compacts = (\<lambda>x. {a. Rep_compact_basis a \<sqsubseteq> x})"

lemma ideal_compacts: "compact_le.ideal (compacts w)"
unfolding compacts_def
 apply (rule compact_le.idealI)
   apply (rule_tac x="Abs_compact_basis (approx 0\<cdot>w)" in exI)
   apply (simp add: approx_less)
  apply simp
  apply (cut_tac a=x in compact_Rep_compact_basis)
  apply (cut_tac a=y in compact_Rep_compact_basis)
  apply (drule bifinite_compact_eq_approx)
  apply (drule bifinite_compact_eq_approx)
  apply (clarify, rename_tac i j)
  apply (rule_tac x="Abs_compact_basis (approx (max i j)\<cdot>w)" in exI)
  apply (simp add: approx_less compact_le_def)
  apply (erule subst, erule subst)
  apply (simp add: monofun_cfun chain_mono [OF chain_approx])
 apply (simp add: compact_le_def)
 apply (erule (1) trans_less)
done

lemma compacts_Rep_compact_basis:
  "compacts (Rep_compact_basis b) = {a. compact_le a b}"
unfolding compacts_def compact_le_def ..

lemma cont_compacts: "cont compacts"
unfolding compacts_def
apply (rule contI2)
apply (rule monofunI)
apply (simp add: set_cpo_simps)
apply (fast intro: trans_less)
apply (simp add: set_cpo_simps)
apply clarify
apply simp
apply (erule (1) compactD2 [OF compact_Rep_compact_basis])
done

lemma compacts_lessD: "compacts x \<subseteq> compacts y \<Longrightarrow> x \<sqsubseteq> y"
apply (subgoal_tac "(\<Squnion>i. approx i\<cdot>x) \<sqsubseteq> y", simp)
apply (rule admD, simp, simp)
apply (drule_tac c="Abs_compact_basis (approx i\<cdot>x)" in subsetD)
apply (simp add: compacts_def Abs_compact_basis_inverse approx_less)
apply (simp add: compacts_def Abs_compact_basis_inverse)
done

lemma compacts_mono: "x \<sqsubseteq> y \<Longrightarrow> compacts x \<subseteq> compacts y"
unfolding compacts_def by (fast intro: trans_less)

lemma less_compact_basis_iff: "(x \<sqsubseteq> y) = (compacts x \<subseteq> compacts y)"
by (rule iffI [OF compacts_mono compacts_lessD])

lemma compact_basis_induct:
  "\<lbrakk>adm P; \<And>a. P (Rep_compact_basis a)\<rbrakk> \<Longrightarrow> P x"
apply (erule approx_induct)
apply (drule_tac x="Abs_compact_basis (approx n\<cdot>x)" in meta_spec)
apply (simp add: Abs_compact_basis_inverse)
done

text {* approximation on compact bases *}

definition
  compact_approx :: "nat \<Rightarrow> 'a compact_basis \<Rightarrow> 'a compact_basis" where
  "compact_approx = (\<lambda>n a. Abs_compact_basis (approx n\<cdot>(Rep_compact_basis a)))"

lemma Rep_compact_approx:
  "Rep_compact_basis (compact_approx n a) = approx n\<cdot>(Rep_compact_basis a)"
unfolding compact_approx_def
by (simp add: Abs_compact_basis_inverse)

lemmas approx_Rep_compact_basis = Rep_compact_approx [symmetric]

lemma compact_approx_le:
  "compact_le (compact_approx n a) a"
unfolding compact_le_def
by (simp add: Rep_compact_approx approx_less)

lemma compact_approx_mono1:
  "i \<le> j \<Longrightarrow> compact_le (compact_approx i a) (compact_approx j a)"
unfolding compact_le_def
apply (simp add: Rep_compact_approx)
apply (rule chain_mono, simp, assumption)
done

lemma compact_approx_mono:
  "compact_le a b \<Longrightarrow> compact_le (compact_approx n a) (compact_approx n b)"
unfolding compact_le_def
apply (simp add: Rep_compact_approx)
apply (erule monofun_cfun_arg)
done

lemma ex_compact_approx_eq: "\<exists>n. compact_approx n a = a"
apply (simp add: Rep_compact_basis_inject [symmetric])
apply (simp add: Rep_compact_approx)
apply (rule bifinite_compact_eq_approx)
apply (rule compact_Rep_compact_basis)
done

lemma compact_approx_idem:
  "compact_approx n (compact_approx n a) = compact_approx n a"
apply (rule Rep_compact_basis_inject [THEN iffD1])
apply (simp add: Rep_compact_approx)
done

lemma finite_fixes_compact_approx: "finite {a. compact_approx n a = a}"
apply (subgoal_tac "finite (Rep_compact_basis ` {a. compact_approx n a = a})")
apply (erule finite_imageD)
apply (rule inj_onI, simp add: Rep_compact_basis_inject)
apply (rule finite_subset [OF _ finite_fixes_approx [where i=n]])
apply (rule subsetI, clarify, rename_tac a)
apply (simp add: Rep_compact_basis_inject [symmetric])
apply (simp add: Rep_compact_approx)
done

lemma finite_range_compact_approx: "finite (range (compact_approx n))"
apply (cut_tac n=n in finite_fixes_compact_approx)
apply (simp add: idem_fixes_eq_range compact_approx_idem)
apply (simp add: image_def)
done

interpretation compact_basis:
  bifinite_basis [compact_le Rep_compact_basis compacts compact_approx]
apply unfold_locales
apply (rule ideal_compacts)
apply (rule cont_compacts)
apply (rule compacts_Rep_compact_basis)
apply (erule compacts_lessD)
apply (rule compact_approx_le)
apply (rule compact_approx_idem)
apply (erule compact_approx_mono)
apply (rule compact_approx_mono1, simp)
apply (rule finite_range_compact_approx)
apply (rule ex_compact_approx_eq)
done


subsection {* A compact basis for powerdomains *}

typedef 'a pd_basis =
  "{S::'a::bifinite compact_basis set. finite S \<and> S \<noteq> {}}"
by (rule_tac x="{arbitrary}" in exI, simp)

lemma finite_Rep_pd_basis [simp]: "finite (Rep_pd_basis u)"
by (insert Rep_pd_basis [of u, unfolded pd_basis_def]) simp

lemma Rep_pd_basis_nonempty [simp]: "Rep_pd_basis u \<noteq> {}"
by (insert Rep_pd_basis [of u, unfolded pd_basis_def]) simp

text {* unit and plus *}

definition
  PDUnit :: "'a compact_basis \<Rightarrow> 'a pd_basis" where
  "PDUnit = (\<lambda>x. Abs_pd_basis {x})"

definition
  PDPlus :: "'a pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> 'a pd_basis" where
  "PDPlus t u = Abs_pd_basis (Rep_pd_basis t \<union> Rep_pd_basis u)"

lemma Rep_PDUnit:
  "Rep_pd_basis (PDUnit x) = {x}"
unfolding PDUnit_def by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

lemma Rep_PDPlus:
  "Rep_pd_basis (PDPlus u v) = Rep_pd_basis u \<union> Rep_pd_basis v"
unfolding PDPlus_def by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

lemma PDUnit_inject [simp]: "(PDUnit a = PDUnit b) = (a = b)"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDUnit by simp

lemma PDPlus_assoc: "PDPlus (PDPlus t u) v = PDPlus t (PDPlus u v)"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_assoc)

lemma PDPlus_commute: "PDPlus t u = PDPlus u t"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_commute)

lemma PDPlus_absorb: "PDPlus t t = t"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_absorb)

lemma pd_basis_induct1:
  assumes PDUnit: "\<And>a. P (PDUnit a)"
  assumes PDPlus: "\<And>a t. P t \<Longrightarrow> P (PDPlus (PDUnit a) t)"
  shows "P x"
apply (induct x, unfold pd_basis_def, clarify)
apply (erule (1) finite_ne_induct)
apply (cut_tac a=x in PDUnit)
apply (simp add: PDUnit_def)
apply (drule_tac a=x in PDPlus)
apply (simp add: PDUnit_def PDPlus_def Abs_pd_basis_inverse [unfolded pd_basis_def])
done

lemma pd_basis_induct:
  assumes PDUnit: "\<And>a. P (PDUnit a)"
  assumes PDPlus: "\<And>t u. \<lbrakk>P t; P u\<rbrakk> \<Longrightarrow> P (PDPlus t u)"
  shows "P x"
apply (induct x rule: pd_basis_induct1)
apply (rule PDUnit, erule PDPlus [OF PDUnit])
done

text {* fold-pd *}

definition
  fold_pd ::
    "('a compact_basis \<Rightarrow> 'b::type) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a pd_basis \<Rightarrow> 'b"
  where "fold_pd g f t = fold1 f (g ` Rep_pd_basis t)"

lemma (in ab_semigroup_idem_mult) fold_pd_PDUnit:
  "fold_pd g (op *) (PDUnit x) = g x"
unfolding fold_pd_def Rep_PDUnit by simp

lemma (in ab_semigroup_idem_mult) fold_pd_PDPlus:
  "fold_pd g (op *) (PDPlus t u) = fold_pd g (op *) t * fold_pd g (op *) u"
unfolding fold_pd_def Rep_PDPlus by (simp add: image_Un fold1_Un2)

text {* approx-pd *}

definition
  approx_pd :: "nat \<Rightarrow> 'a pd_basis \<Rightarrow> 'a pd_basis" where
  "approx_pd n = (\<lambda>t. Abs_pd_basis (compact_approx n ` Rep_pd_basis t))"

lemma Rep_approx_pd:
  "Rep_pd_basis (approx_pd n t) = compact_approx n ` Rep_pd_basis t"
unfolding approx_pd_def
apply (rule Abs_pd_basis_inverse)
apply (simp add: pd_basis_def)
done

lemma approx_pd_simps [simp]:
  "approx_pd n (PDUnit a) = PDUnit (compact_approx n a)"
  "approx_pd n (PDPlus t u) = PDPlus (approx_pd n t) (approx_pd n u)"
apply (simp_all add: Rep_pd_basis_inject [symmetric])
apply (simp_all add: Rep_approx_pd Rep_PDUnit Rep_PDPlus image_Un)
done

lemma approx_pd_idem: "approx_pd n (approx_pd n t) = approx_pd n t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_approx_idem)
apply simp
done

lemma range_image_f: "range (image f) = Pow (range f)"
apply (safe, fast)
apply (rule_tac x="f -` x" in range_eqI)
apply (simp, fast)
done

lemma finite_range_approx_pd: "finite (range (approx_pd n))"
apply (subgoal_tac "finite (Rep_pd_basis ` range (approx_pd n))")
apply (erule finite_imageD)
apply (rule inj_onI, simp add: Rep_pd_basis_inject)
apply (subst image_image)
apply (subst Rep_approx_pd)
apply (simp only: range_composition)
apply (rule finite_subset [OF image_mono [OF subset_UNIV]])
apply (simp add: range_image_f)
apply (rule finite_range_compact_approx)
done

lemma ex_approx_pd_eq: "\<exists>n. approx_pd n t = t"
apply (subgoal_tac "\<exists>n. \<forall>m\<ge>n. approx_pd m t = t", fast)
apply (induct t rule: pd_basis_induct)
apply (cut_tac a=a in ex_compact_approx_eq)
apply (clarify, rule_tac x=n in exI)
apply (clarify, simp)
apply (rule compact_le_antisym)
apply (rule compact_approx_le)
apply (drule_tac a=a in compact_approx_mono1)
apply simp
apply (clarify, rename_tac i j)
apply (rule_tac x="max i j" in exI, simp)
done

end
