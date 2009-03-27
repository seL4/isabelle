(*  Title:      HOLCF/CompactBasis.thy
    Author:     Brian Huffman
*)

header {* Compact bases of domains *}

theory CompactBasis
imports Completion
begin

subsection {* Compact bases of bifinite domains *}

defaultsort profinite

typedef (open) 'a compact_basis = "{x::'a::profinite. compact x}"
by (fast intro: compact_approx)

lemma compact_Rep_compact_basis: "compact (Rep_compact_basis a)"
by (rule Rep_compact_basis [unfolded mem_Collect_eq])

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

text {* Take function for compact basis *}

definition
  compact_take :: "nat \<Rightarrow> 'a compact_basis \<Rightarrow> 'a compact_basis" where
  "compact_take = (\<lambda>n a. Abs_compact_basis (approx n\<cdot>(Rep_compact_basis a)))"

lemma Rep_compact_take:
  "Rep_compact_basis (compact_take n a) = approx n\<cdot>(Rep_compact_basis a)"
unfolding compact_take_def
by (simp add: Abs_compact_basis_inverse)

lemmas approx_Rep_compact_basis = Rep_compact_take [symmetric]

interpretation compact_basis:
  basis_take sq_le compact_take
proof
  fix n :: nat and a :: "'a compact_basis"
  show "compact_take n a \<sqsubseteq> a"
    unfolding compact_le_def
    by (simp add: Rep_compact_take approx_less)
next
  fix n :: nat and a :: "'a compact_basis"
  show "compact_take n (compact_take n a) = compact_take n a"
    by (simp add: Rep_compact_basis_inject [symmetric] Rep_compact_take)
next
  fix n :: nat and a b :: "'a compact_basis"
  assume "a \<sqsubseteq> b" thus "compact_take n a \<sqsubseteq> compact_take n b"
    unfolding compact_le_def Rep_compact_take
    by (rule monofun_cfun_arg)
next
  fix n :: nat and a :: "'a compact_basis"
  show "\<And>n a. compact_take n a \<sqsubseteq> compact_take (Suc n) a"
    unfolding compact_le_def Rep_compact_take
    by (rule chainE, simp)
next
  fix n :: nat
  show "finite (range (compact_take n))"
    apply (rule finite_imageD [where f="Rep_compact_basis"])
    apply (rule finite_subset [where B="range (\<lambda>x. approx n\<cdot>x)"])
    apply (clarsimp simp add: Rep_compact_take)
    apply (rule finite_range_approx)
    apply (rule inj_onI, simp add: Rep_compact_basis_inject)
    done
next
  fix a :: "'a compact_basis"
  show "\<exists>n. compact_take n a = a"
    apply (simp add: Rep_compact_basis_inject [symmetric])
    apply (simp add: Rep_compact_take)
    apply (rule profinite_compact_eq_approx)
    apply (rule compact_Rep_compact_basis)
    done
qed

text {* Ideal completion *}

definition
  approximants :: "'a \<Rightarrow> 'a compact_basis set" where
  "approximants = (\<lambda>x. {a. Rep_compact_basis a \<sqsubseteq> x})"

interpretation compact_basis:
  ideal_completion sq_le compact_take Rep_compact_basis approximants
proof
  fix w :: 'a
  show "preorder.ideal sq_le (approximants w)"
  proof (rule sq_le.idealI)
    show "\<exists>x. x \<in> approximants w"
      unfolding approximants_def
      apply (rule_tac x="Abs_compact_basis (approx 0\<cdot>w)" in exI)
      apply (simp add: Abs_compact_basis_inverse approx_less)
      done
  next
    fix x y :: "'a compact_basis"
    assume "x \<in> approximants w" "y \<in> approximants w"
    thus "\<exists>z \<in> approximants w. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
      unfolding approximants_def
      apply simp
      apply (cut_tac a=x in compact_Rep_compact_basis)
      apply (cut_tac a=y in compact_Rep_compact_basis)
      apply (drule profinite_compact_eq_approx)
      apply (drule profinite_compact_eq_approx)
      apply (clarify, rename_tac i j)
      apply (rule_tac x="Abs_compact_basis (approx (max i j)\<cdot>w)" in exI)
      apply (simp add: compact_le_def)
      apply (simp add: Abs_compact_basis_inverse approx_less)
      apply (erule subst, erule subst)
      apply (simp add: monofun_cfun chain_mono [OF chain_approx])
      done
  next
    fix x y :: "'a compact_basis"
    assume "x \<sqsubseteq> y" "y \<in> approximants w" thus "x \<in> approximants w"
      unfolding approximants_def
      apply simp
      apply (simp add: compact_le_def)
      apply (erule (1) trans_less)
      done
  qed
next
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y"
  show "approximants (\<Squnion>i. Y i) = (\<Union>i. approximants (Y i))"
    unfolding approximants_def
    apply safe
    apply (simp add: compactD2 [OF compact_Rep_compact_basis Y])
    apply (erule trans_less, rule is_ub_thelub [OF Y])
    done
next
  fix a :: "'a compact_basis"
  show "approximants (Rep_compact_basis a) = {b. b \<sqsubseteq> a}"
    unfolding approximants_def compact_le_def ..
next
  fix x y :: "'a"
  assume "approximants x \<subseteq> approximants y" thus "x \<sqsubseteq> y"
    apply (subgoal_tac "(\<Squnion>i. approx i\<cdot>x) \<sqsubseteq> y", simp)
    apply (rule admD, simp, simp)
    apply (drule_tac c="Abs_compact_basis (approx i\<cdot>x)" in subsetD)
    apply (simp add: approximants_def Abs_compact_basis_inverse approx_less)
    apply (simp add: approximants_def Abs_compact_basis_inverse)
    done
qed

text {* minimal compact element *}

definition
  compact_bot :: "'a::bifinite compact_basis" where
  "compact_bot = Abs_compact_basis \<bottom>"

lemma Rep_compact_bot: "Rep_compact_basis compact_bot = \<bottom>"
unfolding compact_bot_def by (simp add: Abs_compact_basis_inverse)

lemma compact_bot_minimal [simp]: "compact_bot \<sqsubseteq> a"
unfolding compact_le_def Rep_compact_bot by simp


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
  assumes "ab_semigroup_idem_mult f"
  shows "fold_pd g f (PDUnit x) = g x"
unfolding fold_pd_def Rep_PDUnit by simp

lemma fold_pd_PDPlus:
  assumes "ab_semigroup_idem_mult f"
  shows "fold_pd g f (PDPlus t u) = f (fold_pd g f t) (fold_pd g f u)"
proof -
  interpret ab_semigroup_idem_mult f by fact
  show ?thesis unfolding fold_pd_def Rep_PDPlus by (simp add: image_Un fold1_Un2)
qed

text {* Take function for powerdomain basis *}

definition
  pd_take :: "nat \<Rightarrow> 'a pd_basis \<Rightarrow> 'a pd_basis" where
  "pd_take n = (\<lambda>t. Abs_pd_basis (compact_take n ` Rep_pd_basis t))"

lemma Rep_pd_take:
  "Rep_pd_basis (pd_take n t) = compact_take n ` Rep_pd_basis t"
unfolding pd_take_def
apply (rule Abs_pd_basis_inverse)
apply (simp add: pd_basis_def)
done

lemma pd_take_simps [simp]:
  "pd_take n (PDUnit a) = PDUnit (compact_take n a)"
  "pd_take n (PDPlus t u) = PDPlus (pd_take n t) (pd_take n u)"
apply (simp_all add: Rep_pd_basis_inject [symmetric])
apply (simp_all add: Rep_pd_take Rep_PDUnit Rep_PDPlus image_Un)
done

lemma pd_take_idem: "pd_take n (pd_take n t) = pd_take n t"
apply (induct t rule: pd_basis_induct)
apply (simp add: compact_basis.take_take)
apply simp
done

lemma finite_range_pd_take: "finite (range (pd_take n))"
apply (rule finite_imageD [where f="Rep_pd_basis"])
apply (rule finite_subset [where B="Pow (range (compact_take n))"])
apply (clarsimp simp add: Rep_pd_take)
apply (simp add: compact_basis.finite_range_take)
apply (rule inj_onI, simp add: Rep_pd_basis_inject)
done

lemma pd_take_covers: "\<exists>n. pd_take n t = t"
apply (subgoal_tac "\<exists>n. \<forall>m\<ge>n. pd_take m t = t", fast)
apply (induct t rule: pd_basis_induct)
apply (cut_tac a=a in compact_basis.take_covers)
apply (clarify, rule_tac x=n in exI)
apply (clarify, simp)
apply (rule antisym_less)
apply (rule compact_basis.take_less)
apply (drule_tac a=a in compact_basis.take_chain_le)
apply simp
apply (clarify, rename_tac i j)
apply (rule_tac x="max i j" in exI, simp)
done

end
