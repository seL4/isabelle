(*  Title:      HOLCF/Sum_Cpo.thy
    Author:     Brian Huffman
*)

header {* The cpo of disjoint sums *}

theory Sum_Cpo
imports Bifinite
begin

subsection {* Ordering on type @{typ "'a + 'b"} *}

instantiation "+" :: (sq_ord, sq_ord) sq_ord
begin

definition
  less_sum_def: "x \<sqsubseteq> y \<equiv> case x of
         Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> a \<sqsubseteq> b | Inr b \<Rightarrow> False) |
         Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> False | Inr b \<Rightarrow> a \<sqsubseteq> b)"

instance ..
end

lemma Inl_less_iff [simp]: "Inl x \<sqsubseteq> Inl y = x \<sqsubseteq> y"
unfolding less_sum_def by simp

lemma Inr_less_iff [simp]: "Inr x \<sqsubseteq> Inr y = x \<sqsubseteq> y"
unfolding less_sum_def by simp

lemma Inl_less_Inr [simp]: "\<not> Inl x \<sqsubseteq> Inr y"
unfolding less_sum_def by simp

lemma Inr_less_Inl [simp]: "\<not> Inr x \<sqsubseteq> Inl y"
unfolding less_sum_def by simp

lemma Inl_mono: "x \<sqsubseteq> y \<Longrightarrow> Inl x \<sqsubseteq> Inl y"
by simp

lemma Inr_mono: "x \<sqsubseteq> y \<Longrightarrow> Inr x \<sqsubseteq> Inr y"
by simp

lemma Inl_lessE: "\<lbrakk>Inl a \<sqsubseteq> x; \<And>b. \<lbrakk>x = Inl b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (cases x, simp_all)

lemma Inr_lessE: "\<lbrakk>Inr a \<sqsubseteq> x; \<And>b. \<lbrakk>x = Inr b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (cases x, simp_all)

lemmas sum_less_elims = Inl_lessE Inr_lessE

lemma sum_less_cases:
  "\<lbrakk>x \<sqsubseteq> y;
    \<And>a b. \<lbrakk>x = Inl a; y = Inl b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R;
    \<And>a b. \<lbrakk>x = Inr a; y = Inr b; a \<sqsubseteq> b\<rbrakk> \<Longrightarrow> R\<rbrakk>
      \<Longrightarrow> R"
by (cases x, safe elim!: sum_less_elims, auto)

subsection {* Sum type is a complete partial order *}

instance "+" :: (po, po) po
proof
  fix x :: "'a + 'b"
  show "x \<sqsubseteq> x"
    by (induct x, simp_all)
next
  fix x y :: "'a + 'b"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> x" thus "x = y"
    by (induct x, auto elim!: sum_less_elims intro: antisym_less)
next
  fix x y z :: "'a + 'b"
  assume "x \<sqsubseteq> y" and "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    by (induct x, auto elim!: sum_less_elims intro: trans_less)
qed

lemma monofun_inv_Inl: "monofun (\<lambda>p. THE a. p = Inl a)"
by (rule monofunI, erule sum_less_cases, simp_all)

lemma monofun_inv_Inr: "monofun (\<lambda>p. THE b. p = Inr b)"
by (rule monofunI, erule sum_less_cases, simp_all)

lemma sum_chain_cases:
  assumes Y: "chain Y"
  assumes A: "\<And>A. \<lbrakk>chain A; Y = (\<lambda>i. Inl (A i))\<rbrakk> \<Longrightarrow> R"
  assumes B: "\<And>B. \<lbrakk>chain B; Y = (\<lambda>i. Inr (B i))\<rbrakk> \<Longrightarrow> R"
  shows "R"
 apply (cases "Y 0")
  apply (rule A)
   apply (rule ch2ch_monofun [OF monofun_inv_Inl Y])
  apply (rule ext)
  apply (cut_tac j=i in chain_mono [OF Y le0], simp)
  apply (erule Inl_lessE, simp)
 apply (rule B)
  apply (rule ch2ch_monofun [OF monofun_inv_Inr Y])
 apply (rule ext)
 apply (cut_tac j=i in chain_mono [OF Y le0], simp)
 apply (erule Inr_lessE, simp)
done

lemma is_lub_Inl: "range S <<| x \<Longrightarrow> range (\<lambda>i. Inl (S i)) <<| Inl x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_ub_lub)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (erule Inl_lessE, simp)
 apply (erule is_lub_lub)
 apply (rule ub_rangeI)
 apply (drule ub_rangeD, simp)
done

lemma is_lub_Inr: "range S <<| x \<Longrightarrow> range (\<lambda>i. Inr (S i)) <<| Inr x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_ub_lub)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (erule Inr_lessE, simp)
 apply (erule is_lub_lub)
 apply (rule ub_rangeI)
 apply (drule ub_rangeD, simp)
done

instance "+" :: (cpo, cpo) cpo
 apply intro_classes
 apply (erule sum_chain_cases, safe)
  apply (rule exI)
  apply (rule is_lub_Inl)
  apply (erule cpo_lubI)
 apply (rule exI)
 apply (rule is_lub_Inr)
 apply (erule cpo_lubI)
done

subsection {* Continuity of @{term Inl}, @{term Inr}, @{term sum_case} *}

lemma cont_Inl: "cont Inl"
by (intro contI is_lub_Inl cpo_lubI)

lemma cont_Inr: "cont Inr"
by (intro contI is_lub_Inr cpo_lubI)

lemmas cont2cont_Inl [cont2cont] = cont_compose [OF cont_Inl]
lemmas cont2cont_Inr [cont2cont] = cont_compose [OF cont_Inr]

lemmas ch2ch_Inl [simp] = ch2ch_cont [OF cont_Inl]
lemmas ch2ch_Inr [simp] = ch2ch_cont [OF cont_Inr]

lemmas lub_Inl = cont2contlubE [OF cont_Inl, symmetric]
lemmas lub_Inr = cont2contlubE [OF cont_Inr, symmetric]

lemma cont_sum_case1:
  assumes f: "\<And>a. cont (\<lambda>x. f x a)"
  assumes g: "\<And>b. cont (\<lambda>x. g x b)"
  shows "cont (\<lambda>x. case y of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
by (induct y, simp add: f, simp add: g)

lemma cont_sum_case2: "\<lbrakk>cont f; cont g\<rbrakk> \<Longrightarrow> cont (sum_case f g)"
apply (rule contI)
apply (erule sum_chain_cases)
apply (simp add: cont2contlubE [OF cont_Inl, symmetric] contE)
apply (simp add: cont2contlubE [OF cont_Inr, symmetric] contE)
done

lemma cont2cont_sum_case:
  assumes f1: "\<And>a. cont (\<lambda>x. f x a)" and f2: "\<And>x. cont (\<lambda>a. f x a)"
  assumes g1: "\<And>b. cont (\<lambda>x. g x b)" and g2: "\<And>x. cont (\<lambda>b. g x b)"
  assumes h: "cont (\<lambda>x. h x)"
  shows "cont (\<lambda>x. case h x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
apply (rule cont_apply [OF h])
apply (rule cont_sum_case2 [OF f2 g2])
apply (rule cont_sum_case1 [OF f1 g1])
done

lemma cont2cont_sum_case' [cont2cont]:
  assumes f: "cont (\<lambda>p. f (fst p) (snd p))"
  assumes g: "cont (\<lambda>p. g (fst p) (snd p))"
  assumes h: "cont (\<lambda>x. h x)"
  shows "cont (\<lambda>x. case h x of Inl a \<Rightarrow> f x a | Inr b \<Rightarrow> g x b)"
proof -
  note f1 = f [THEN cont_fst_snd_D1]
  note f2 = f [THEN cont_fst_snd_D2]
  note g1 = g [THEN cont_fst_snd_D1]
  note g2 = g [THEN cont_fst_snd_D2]
  show ?thesis
    apply (rule cont_apply [OF h])
    apply (rule cont_sum_case2 [OF f2 g2])
    apply (rule cont_sum_case1 [OF f1 g1])
    done
qed

subsection {* Compactness and chain-finiteness *}

lemma compact_Inl: "compact a \<Longrightarrow> compact (Inl a)"
apply (rule compactI2)
apply (erule sum_chain_cases, safe)
apply (simp add: lub_Inl)
apply (erule (2) compactD2)
apply (simp add: lub_Inr)
done

lemma compact_Inr: "compact a \<Longrightarrow> compact (Inr a)"
apply (rule compactI2)
apply (erule sum_chain_cases, safe)
apply (simp add: lub_Inl)
apply (simp add: lub_Inr)
apply (erule (2) compactD2)
done

lemma compact_Inl_rev: "compact (Inl a) \<Longrightarrow> compact a"
unfolding compact_def
by (drule adm_subst [OF cont_Inl], simp)

lemma compact_Inr_rev: "compact (Inr a) \<Longrightarrow> compact a"
unfolding compact_def
by (drule adm_subst [OF cont_Inr], simp)

lemma compact_Inl_iff [simp]: "compact (Inl a) = compact a"
by (safe elim!: compact_Inl compact_Inl_rev)

lemma compact_Inr_iff [simp]: "compact (Inr a) = compact a"
by (safe elim!: compact_Inr compact_Inr_rev)

instance "+" :: (chfin, chfin) chfin
apply intro_classes
apply (erule compact_imp_max_in_chain)
apply (case_tac "\<Squnion>i. Y i", simp_all)
done

instance "+" :: (finite_po, finite_po) finite_po ..

instance "+" :: (discrete_cpo, discrete_cpo) discrete_cpo
by intro_classes (simp add: less_sum_def split: sum.split)

subsection {* Sum type is a bifinite domain *}

instantiation "+" :: (profinite, profinite) profinite
begin

definition
  approx_sum_def: "approx =
    (\<lambda>n. \<Lambda> x. case x of Inl a \<Rightarrow> Inl (approx n\<cdot>a) | Inr b \<Rightarrow> Inr (approx n\<cdot>b))"

lemma approx_Inl [simp]: "approx n\<cdot>(Inl x) = Inl (approx n\<cdot>x)"
  unfolding approx_sum_def by simp

lemma approx_Inr [simp]: "approx n\<cdot>(Inr x) = Inr (approx n\<cdot>x)"
  unfolding approx_sum_def by simp

instance proof
  fix i :: nat and x :: "'a + 'b"
  show "chain (approx :: nat \<Rightarrow> 'a + 'b \<rightarrow> 'a + 'b)"
    unfolding approx_sum_def
    by (rule ch2ch_LAM, case_tac x, simp_all)
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    by (induct x, simp_all add: lub_Inl lub_Inr)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    by (induct x, simp_all)
  have "{x::'a + 'b. approx i\<cdot>x = x} \<subseteq>
        {x::'a. approx i\<cdot>x = x} <+> {x::'b. approx i\<cdot>x = x}"
    by (rule subsetI, case_tac x, simp_all add: InlI InrI)
  thus "finite {x::'a + 'b. approx i\<cdot>x = x}"
    by (rule finite_subset,
        intro finite_Plus finite_fixes_approx)
qed

end

end
