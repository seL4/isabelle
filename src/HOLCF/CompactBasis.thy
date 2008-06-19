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
  fixes r :: "'a::type \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
  assumes r_refl: "x \<preceq> x"
  assumes r_trans: "\<lbrakk>x \<preceq> y; y \<preceq> z\<rbrakk> \<Longrightarrow> x \<preceq> z"
begin

definition
  ideal :: "'a set \<Rightarrow> bool" where
  "ideal A = ((\<exists>x. x \<in> A) \<and> (\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z) \<and>
    (\<forall>x y. x \<preceq> y \<longrightarrow> y \<in> A \<longrightarrow> x \<in> A))"

lemma idealI:
  assumes "\<exists>x. x \<in> A"
  assumes "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z"
  assumes "\<And>x y. \<lbrakk>x \<preceq> y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
  shows "ideal A"
unfolding ideal_def using prems by fast

lemma idealD1:
  "ideal A \<Longrightarrow> \<exists>x. x \<in> A"
unfolding ideal_def by fast

lemma idealD2:
  "\<lbrakk>ideal A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. x \<preceq> z \<and> y \<preceq> z"
unfolding ideal_def by fast

lemma idealD3:
  "\<lbrakk>ideal A; x \<preceq> y; y \<in> A\<rbrakk> \<Longrightarrow> x \<in> A"
unfolding ideal_def by fast

lemma ideal_directed_finite:
  assumes A: "ideal A"
  shows "\<lbrakk>finite U; U \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>z\<in>A. \<forall>x\<in>U. x \<preceq> z"
apply (induct U set: finite)
apply (simp add: idealD1 [OF A])
apply (simp, clarify, rename_tac y)
apply (drule (1) idealD2 [OF A])
apply (clarify, erule_tac x=z in rev_bexI)
apply (fast intro: r_trans)
done

lemma ideal_principal: "ideal {x. x \<preceq> z}"
apply (rule idealI)
apply (rule_tac x=z in exI)
apply (fast intro: r_refl)
apply (rule_tac x=z in bexI, fast)
apply (fast intro: r_refl)
apply (fast intro: r_trans)
done

lemma ex_ideal: "\<exists>A. ideal A"
by (rule exI, rule ideal_principal)

lemma directed_image_ideal:
  assumes A: "ideal A"
  assumes f: "\<And>x y. x \<preceq> y \<Longrightarrow> f x \<sqsubseteq> f y"
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

lemma lub_image_principal:
  assumes f: "\<And>x y. x \<preceq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  shows "(\<Squnion>x\<in>{x. x \<preceq> y}. f x) = f y"
apply (rule thelubI)
apply (rule is_lub_maximal)
apply (rule ub_imageI)
apply (simp add: f)
apply (rule imageI)
apply (simp add: r_refl)
done

end

interpretation sq_le: preorder ["sq_le :: 'a::po \<Rightarrow> 'a \<Rightarrow> bool"]
apply unfold_locales
apply (rule refl_less)
apply (erule (1) trans_less)
done

subsection {* Defining functions in terms of basis elements *}

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

locale basis_take = preorder +
  fixes take :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'a"
  assumes take_less: "take n a \<preceq> a"
  assumes take_take: "take n (take n a) = take n a"
  assumes take_mono: "a \<preceq> b \<Longrightarrow> take n a \<preceq> take n b"
  assumes take_chain: "take n a \<preceq> take (Suc n) a"
  assumes finite_range_take: "finite (range (take n))"
  assumes take_covers: "\<exists>n. take n a = a"
begin

lemma take_chain_less: "m < n \<Longrightarrow> take m a \<preceq> take n a"
by (erule less_Suc_induct, rule take_chain, erule (1) r_trans)

lemma take_chain_le: "m \<le> n \<Longrightarrow> take m a \<preceq> take n a"
by (cases "m = n", simp add: r_refl, simp add: take_chain_less)

end

locale ideal_completion = basis_take +
  fixes principal :: "'a::type \<Rightarrow> 'b::cpo"
  fixes rep :: "'b::cpo \<Rightarrow> 'a::type set"
  assumes ideal_rep: "\<And>x. preorder.ideal r (rep x)"
  assumes cont_rep: "cont rep"
  assumes rep_principal: "\<And>a. rep (principal a) = {b. b \<preceq> a}"
  assumes subset_repD: "\<And>x y. rep x \<subseteq> rep y \<Longrightarrow> x \<sqsubseteq> y"
begin

lemma finite_take_rep: "finite (take n ` rep x)"
by (rule finite_subset [OF image_mono [OF subset_UNIV] finite_range_take])

lemma basis_fun_lemma0:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "\<exists>u. f ` take i ` rep x <<| u"
apply (rule finite_directed_has_lub)
apply (rule finite_imageI)
apply (rule finite_take_rep)
apply (subst image_image)
apply (rule directed_image_ideal)
apply (rule ideal_rep)
apply (rule f_mono)
apply (erule take_mono)
done

lemma basis_fun_lemma1:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "chain (\<lambda>i. lub (f ` take i ` rep x))"
 apply (rule chainI)
 apply (rule is_lub_thelub0)
  apply (rule basis_fun_lemma0, erule f_mono)
 apply (rule is_ubI, clarsimp, rename_tac a)
 apply (rule sq_le.trans_less [OF f_mono [OF take_chain]])
 apply (rule is_ub_thelub0)
  apply (rule basis_fun_lemma0, erule f_mono)
 apply simp
done

lemma basis_fun_lemma2:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "f ` rep x <<| (\<Squnion>i. lub (f ` take i ` rep x))"
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
 apply (rule sq_le.trans_less [OF f_mono [OF take_less]])
 apply (erule (1) ub_imageD)
done

lemma basis_fun_lemma:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "\<exists>u. f ` rep x <<| u"
by (rule exI, rule basis_fun_lemma2, erule f_mono)

lemma rep_mono: "x \<sqsubseteq> y \<Longrightarrow> rep x \<subseteq> rep y"
apply (drule cont_rep [THEN cont2mono, THEN monofunE])
apply (simp add: set_cpo_simps)
done

lemma rep_contlub:
  "chain Y \<Longrightarrow> rep (\<Squnion>i. Y i) = (\<Union>i. rep (Y i))"
by (simp add: cont2contlubE [OF cont_rep] set_cpo_simps)

lemma less_def: "x \<sqsubseteq> y \<longleftrightarrow> rep x \<subseteq> rep y"
by (rule iffI [OF rep_mono subset_repD])

lemma rep_eq: "rep x = {a. principal a \<sqsubseteq> x}"
unfolding less_def rep_principal
apply safe
apply (erule (1) idealD3 [OF ideal_rep])
apply (erule subsetD, simp add: r_refl)
done

lemma mem_rep_iff_principal_less: "a \<in> rep x \<longleftrightarrow> principal a \<sqsubseteq> x"
by (simp add: rep_eq)

lemma principal_less_iff_mem_rep: "principal a \<sqsubseteq> x \<longleftrightarrow> a \<in> rep x"
by (simp add: rep_eq)

lemma principal_less_iff: "principal a \<sqsubseteq> principal b \<longleftrightarrow> a \<preceq> b"
by (simp add: principal_less_iff_mem_rep rep_principal)

lemma principal_eq_iff: "principal a = principal b \<longleftrightarrow> a \<preceq> b \<and> b \<preceq> a"
unfolding po_eq_conv [where 'a='b] principal_less_iff ..

lemma repD: "a \<in> rep x \<Longrightarrow> principal a \<sqsubseteq> x"
by (simp add: rep_eq)

lemma principal_mono: "a \<preceq> b \<Longrightarrow> principal a \<sqsubseteq> principal b"
by (simp add: principal_less_iff)

lemma lessI: "(\<And>a. principal a \<sqsubseteq> x \<Longrightarrow> principal a \<sqsubseteq> u) \<Longrightarrow> x \<sqsubseteq> u"
unfolding principal_less_iff_mem_rep
by (simp add: less_def subset_eq)

lemma lub_principal_rep: "principal ` rep x <<| x"
apply (rule is_lubI)
apply (rule ub_imageI)
apply (erule repD)
apply (subst less_def)
apply (rule subsetI)
apply (drule (1) ub_imageD)
apply (simp add: rep_eq)
done

definition
  basis_fun :: "('a::type \<Rightarrow> 'c::cpo) \<Rightarrow> 'b \<rightarrow> 'c" where
  "basis_fun = (\<lambda>f. (\<Lambda> x. lub (f ` rep x)))"

lemma basis_fun_beta:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>x = lub (f ` rep x)"
unfolding basis_fun_def
proof (rule beta_cfun)
  have lub: "\<And>x. \<exists>u. f ` rep x <<| u"
    using f_mono by (rule basis_fun_lemma)
  show cont: "cont (\<lambda>x. lub (f ` rep x))"
    apply (rule contI2)
     apply (rule monofunI)
     apply (rule is_lub_thelub0 [OF lub ub_imageI])
     apply (rule is_ub_thelub0 [OF lub imageI])
     apply (erule (1) subsetD [OF rep_mono])
    apply (rule is_lub_thelub0 [OF lub ub_imageI])
    apply (simp add: rep_contlub, clarify)
    apply (erule rev_trans_less [OF is_ub_thelub])
    apply (erule is_ub_thelub0 [OF lub imageI])
    done
qed

lemma basis_fun_principal:
  fixes f :: "'a::type \<Rightarrow> 'c::cpo"
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "basis_fun f\<cdot>(principal a) = f a"
apply (subst basis_fun_beta, erule f_mono)
apply (subst rep_principal)
apply (rule lub_image_principal, erule f_mono)
done

lemma basis_fun_mono:
  assumes f_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  assumes g_mono: "\<And>a b. a \<preceq> b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes less: "\<And>a. f a \<sqsubseteq> g a"
  shows "basis_fun f \<sqsubseteq> basis_fun g"
 apply (rule less_cfun_ext)
 apply (simp only: basis_fun_beta f_mono g_mono)
 apply (rule is_lub_thelub0)
  apply (rule basis_fun_lemma, erule f_mono)
 apply (rule ub_imageI, rename_tac a)
 apply (rule sq_le.trans_less [OF less])
 apply (rule is_ub_thelub0)
  apply (rule basis_fun_lemma, erule g_mono)
 apply (erule imageI)
done

lemma compact_principal: "compact (principal a)"
by (rule compactI2, simp add: principal_less_iff_mem_rep rep_contlub)

definition
  completion_approx :: "nat \<Rightarrow> 'b \<rightarrow> 'b" where
  "completion_approx = (\<lambda>i. basis_fun (\<lambda>a. principal (take i a)))"

lemma completion_approx_beta:
  "completion_approx i\<cdot>x = (\<Squnion>a\<in>rep x. principal (take i a))"
unfolding completion_approx_def
by (simp add: basis_fun_beta principal_mono take_mono)

lemma completion_approx_principal:
  "completion_approx i\<cdot>(principal a) = principal (take i a)"
unfolding completion_approx_def
by (simp add: basis_fun_principal principal_mono take_mono)

lemma chain_completion_approx: "chain completion_approx"
unfolding completion_approx_def
apply (rule chainI)
apply (rule basis_fun_mono)
apply (erule principal_mono [OF take_mono])
apply (erule principal_mono [OF take_mono])
apply (rule principal_mono [OF take_chain])
done

lemma lub_completion_approx: "(\<Squnion>i. completion_approx i\<cdot>x) = x"
unfolding completion_approx_beta
 apply (subst image_image [where f=principal, symmetric])
 apply (rule unique_lub [OF _ lub_principal_rep])
 apply (rule basis_fun_lemma2, erule principal_mono)
done

lemma completion_approx_eq_principal:
  "\<exists>a\<in>rep x. completion_approx i\<cdot>x = principal (take i a)"
unfolding completion_approx_beta
 apply (subst image_image [where f=principal, symmetric])
 apply (subgoal_tac "finite (principal ` take i ` rep x)")
  apply (subgoal_tac "directed (principal ` take i ` rep x)")
   apply (drule (1) lub_finite_directed_in_self, fast)
  apply (subst image_image)
  apply (rule directed_image_ideal)
   apply (rule ideal_rep)
  apply (erule principal_mono [OF take_mono])
 apply (rule finite_imageI)
 apply (rule finite_take_rep)
done

lemma completion_approx_idem:
  "completion_approx i\<cdot>(completion_approx i\<cdot>x) = completion_approx i\<cdot>x"
using completion_approx_eq_principal [where i=i and x=x]
by (auto simp add: completion_approx_principal take_take)

lemma finite_fixes_completion_approx:
  "finite {x. completion_approx i\<cdot>x = x}" (is "finite ?S")
apply (subgoal_tac "?S \<subseteq> principal ` range (take i)")
apply (erule finite_subset)
apply (rule finite_imageI)
apply (rule finite_range_take)
apply (clarify, erule subst)
apply (cut_tac x=x and i=i in completion_approx_eq_principal)
apply fast
done

lemma principal_induct:
  assumes adm: "adm P"
  assumes P: "\<And>a. P (principal a)"
  shows "P x"
 apply (subgoal_tac "P (\<Squnion>i. completion_approx i\<cdot>x)")
 apply (simp add: lub_completion_approx)
 apply (rule admD [OF adm])
  apply (simp add: chain_completion_approx)
 apply (cut_tac x=x and i=i in completion_approx_eq_principal)
 apply (clarify, simp add: P)
done

lemma compact_imp_principal: "compact x \<Longrightarrow> \<exists>a. x = principal a"
apply (drule adm_compact_neq [OF _ cont_id])
apply (drule admD2 [where Y="\<lambda>n. completion_approx n\<cdot>x"])
apply (simp add: chain_completion_approx)
apply (simp add: lub_completion_approx)
apply (erule exE, erule ssubst)
apply (cut_tac i=i and x=x in completion_approx_eq_principal)
apply (clarify, erule exI)
done

end


subsection {* Compact bases of bifinite domains *}

defaultsort profinite

typedef (open) 'a compact_basis = "{x::'a::profinite. compact x}"
by (fast intro: compact_approx)

lemma compact_Rep_compact_basis [simp]: "compact (Rep_compact_basis a)"
by (rule Rep_compact_basis [unfolded mem_Collect_eq])

lemma Rep_Abs_compact_basis_approx [simp]:
  "Rep_compact_basis (Abs_compact_basis (approx n\<cdot>x)) = approx n\<cdot>x"
by (rule Abs_compact_basis_inverse, simp)

lemma compact_imp_Rep_compact_basis:
  "compact x \<Longrightarrow> \<exists>y. x = Rep_compact_basis y"
by (rule exI, rule Abs_compact_basis_inverse [symmetric], simp)

instantiation compact_basis :: (profinite) sq_ord
begin

definition
  compact_le_def:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. Rep_compact_basis x \<sqsubseteq> Rep_compact_basis y)"

instance ..

end

instance compact_basis :: (profinite) po
by (rule typedef_po
    [OF type_definition_compact_basis compact_le_def])

text {* minimal compact element *}

definition
  compact_bot :: "'a::bifinite compact_basis" where
  "compact_bot = Abs_compact_basis \<bottom>"

lemma Rep_compact_bot: "Rep_compact_basis compact_bot = \<bottom>"
unfolding compact_bot_def by (simp add: Abs_compact_basis_inverse)

lemma compact_minimal [simp]: "compact_bot \<sqsubseteq> a"
unfolding compact_le_def Rep_compact_bot by simp

text {* compacts *}

definition
  compacts :: "'a \<Rightarrow> 'a compact_basis set" where
  "compacts = (\<lambda>x. {a. Rep_compact_basis a \<sqsubseteq> x})"

lemma ideal_compacts: "sq_le.ideal (compacts w)"
unfolding compacts_def
 apply (rule sq_le.idealI)
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
  "compacts (Rep_compact_basis b) = {a. a \<sqsubseteq> b}"
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

lemma compact_approx_le: "compact_approx n a \<sqsubseteq> a"
unfolding compact_le_def
by (simp add: Rep_compact_approx approx_less)

lemma compact_approx_mono1:
  "i \<le> j \<Longrightarrow> compact_approx i a \<sqsubseteq> compact_approx j a"
unfolding compact_le_def
apply (simp add: Rep_compact_approx)
apply (rule chain_mono, simp, assumption)
done

lemma compact_approx_mono:
  "a \<sqsubseteq> b \<Longrightarrow> compact_approx n a \<sqsubseteq> compact_approx n b"
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
  ideal_completion [sq_le compact_approx Rep_compact_basis compacts]
proof (unfold_locales)
  fix n :: nat and a b :: "'a compact_basis" and x :: "'a"
  show "compact_approx n a \<sqsubseteq> a"
    by (rule compact_approx_le)
  show "compact_approx n (compact_approx n a) = compact_approx n a"
    by (rule compact_approx_idem)
  show "compact_approx n a \<sqsubseteq> compact_approx (Suc n) a"
    by (rule compact_approx_mono1, simp)
  show "finite (range (compact_approx n))"
    by (rule finite_range_compact_approx)
  show "\<exists>n\<Colon>nat. compact_approx n a = a"
    by (rule ex_compact_approx_eq)
  show "preorder.ideal sq_le (compacts x)"
    by (rule ideal_compacts)
  show "cont compacts"
    by (rule cont_compacts)
  show "compacts (Rep_compact_basis a) = {b. b \<sqsubseteq> a}"
    by (rule compacts_Rep_compact_basis)
next
  fix n :: nat and a b :: "'a compact_basis"
  assume "a \<sqsubseteq> b"
  thus "compact_approx n a \<sqsubseteq> compact_approx n b"
    by (rule compact_approx_mono)
next
  fix x y :: "'a"
  assume "compacts x \<subseteq> compacts y" thus "x \<sqsubseteq> y"
    by (rule compacts_lessD)
qed


subsection {* A compact basis for powerdomains *}

typedef 'a pd_basis =
  "{S::'a::profinite compact_basis set. finite S \<and> S \<noteq> {}}"
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

lemma fold_pd_PDUnit:
  includes ab_semigroup_idem_mult f
  shows "fold_pd g f (PDUnit x) = g x"
unfolding fold_pd_def Rep_PDUnit by simp

lemma fold_pd_PDPlus:
  includes ab_semigroup_idem_mult f
  shows "fold_pd g f (PDPlus t u) = f (fold_pd g f t) (fold_pd g f u)"
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
apply (rule antisym_less)
apply (rule compact_approx_le)
apply (drule_tac a=a in compact_approx_mono1)
apply simp
apply (clarify, rename_tac i j)
apply (rule_tac x="max i j" in exI, simp)
done

end
