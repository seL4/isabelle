(*  Title:      HOLCF/CompactBasis.thy
    Author:     Brian Huffman
*)

header {* A compact basis for powerdomains *}

theory CompactBasis
imports Algebraic
begin

default_sort sfp

subsection {* A compact basis for powerdomains *}

typedef 'a pd_basis =
  "{S::'a compact_basis set. finite S \<and> S \<noteq> {}}"
by (rule_tac x="{arbitrary}" in exI, simp)

lemma finite_Rep_pd_basis [simp]: "finite (Rep_pd_basis u)"
by (insert Rep_pd_basis [of u, unfolded pd_basis_def]) simp

lemma Rep_pd_basis_nonempty [simp]: "Rep_pd_basis u \<noteq> {}"
by (insert Rep_pd_basis [of u, unfolded pd_basis_def]) simp

text {* The powerdomain basis type is countable. *}

lemma pd_basis_countable: "\<exists>f::'a::sfp pd_basis \<Rightarrow> nat. inj f"
proof -
  obtain g :: "'a compact_basis \<Rightarrow> nat" where "inj g"
    using compact_basis.countable ..
  hence image_g_eq: "\<And>A B. g ` A = g ` B \<longleftrightarrow> A = B"
    by (rule inj_image_eq_iff)
  have "inj (\<lambda>t. set_encode (g ` Rep_pd_basis t))"
    by (simp add: inj_on_def set_encode_eq image_g_eq Rep_pd_basis_inject)
  thus ?thesis by - (rule exI)
  (* FIXME: why doesn't ".." or "by (rule exI)" work? *)
qed

subsection {* Unit and plus constructors *}

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
apply (simp add: PDUnit_def PDPlus_def
  Abs_pd_basis_inverse [unfolded pd_basis_def])
done

lemma pd_basis_induct:
  assumes PDUnit: "\<And>a. P (PDUnit a)"
  assumes PDPlus: "\<And>t u. \<lbrakk>P t; P u\<rbrakk> \<Longrightarrow> P (PDPlus t u)"
  shows "P x"
apply (induct x rule: pd_basis_induct1)
apply (rule PDUnit, erule PDPlus [OF PDUnit])
done

subsection {* Fold operator *}

definition
  fold_pd ::
    "('a compact_basis \<Rightarrow> 'b::type) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a pd_basis \<Rightarrow> 'b"
  where "fold_pd g f t = fold1 f (g ` Rep_pd_basis t)"

lemma fold_pd_PDUnit:
  assumes "class.ab_semigroup_idem_mult f"
  shows "fold_pd g f (PDUnit x) = g x"
unfolding fold_pd_def Rep_PDUnit by simp

lemma fold_pd_PDPlus:
  assumes "class.ab_semigroup_idem_mult f"
  shows "fold_pd g f (PDPlus t u) = f (fold_pd g f t) (fold_pd g f u)"
proof -
  interpret ab_semigroup_idem_mult f by fact
  show ?thesis unfolding fold_pd_def Rep_PDPlus
    by (simp add: image_Un fold1_Un2)
qed

subsection {* Lemmas for proving if-and-only-if inequalities *}

lemma chain_max_below_iff:
  assumes Y: "chain Y" shows "Y (max i j) \<sqsubseteq> x \<longleftrightarrow> Y i \<sqsubseteq> x \<and> Y j \<sqsubseteq> x"
apply auto
apply (erule below_trans [OF chain_mono [OF Y le_maxI1]])
apply (erule below_trans [OF chain_mono [OF Y le_maxI2]])
apply (simp add: max_def)
done

lemma all_ex_below_disj_iff:
  assumes "chain X" and "chain Y"
  shows "(\<forall>i. \<exists>j. X i \<sqsubseteq> Z j \<or> Y i \<sqsubseteq> Z j) \<longleftrightarrow>
         (\<forall>i. \<exists>j. X i \<sqsubseteq> Z j) \<or> (\<forall>i. \<exists>j. Y i \<sqsubseteq> Z j)"
by (metis chain_max_below_iff assms)

lemma all_ex_below_conj_iff:
  assumes "chain X" and "chain Y" and "chain Z"
  shows "(\<forall>i. \<exists>j. X i \<sqsubseteq> Z j \<and> Y i \<sqsubseteq> Z j) \<longleftrightarrow>
         (\<forall>i. \<exists>j. X i \<sqsubseteq> Z j) \<and> (\<forall>i. \<exists>j. Y i \<sqsubseteq> Z j)"
oops

end
