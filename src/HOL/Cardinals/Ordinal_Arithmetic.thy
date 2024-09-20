(*  Title:      HOL/Cardinals/Ordinal_Arithmetic.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2014

Ordinal arithmetic.
*)

section \<open>Ordinal Arithmetic\<close>

theory Ordinal_Arithmetic
  imports Wellorder_Constructions
begin

definition osum :: "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a + 'b) rel"  (infixr \<open>+o\<close> 70)
  where
    "r +o r' = map_prod Inl Inl ` r \<union> map_prod Inr Inr ` r' \<union>
     {(Inl a, Inr a') | a a' . a \<in> Field r \<and> a' \<in> Field r'}"

lemma Field_osum: "Field(r +o r') = Inl ` Field r \<union> Inr ` Field r'"
  unfolding osum_def Field_def by auto

lemma osum_Refl:"\<lbrakk>Refl r; Refl r'\<rbrakk> \<Longrightarrow> Refl (r +o r')"
  (*Need first unfold Field_osum, only then osum_def*)
  unfolding refl_on_def Field_osum unfolding osum_def by blast

lemma osum_trans:
  assumes TRANS: "trans r" and TRANS': "trans r'"
  shows "trans (r +o r')"
  unfolding trans_def
proof(safe)
  fix x y z assume *: "(x, y) \<in> r +o r'" "(y, z) \<in> r +o r'"
  thus "(x, z) \<in> r +o r'"
  proof (cases x y z rule: sum.exhaust[case_product sum.exhaust sum.exhaust])
    case (Inl_Inl_Inl a b c)
    with * have "(a,b) \<in> r" "(b,c) \<in> r" unfolding osum_def by auto
    with TRANS have "(a,c) \<in> r" unfolding trans_def by blast
    with Inl_Inl_Inl show ?thesis unfolding osum_def by auto
  next
    case (Inl_Inl_Inr a b c)
    with * have "a \<in> Field r" "c \<in> Field r'" unfolding osum_def Field_def by auto
    with Inl_Inl_Inr show ?thesis unfolding osum_def by auto
  next
    case (Inl_Inr_Inr a b c)
    with * have "a \<in> Field r" "c \<in> Field r'" unfolding osum_def Field_def by auto
    with Inl_Inr_Inr show ?thesis unfolding osum_def by auto
  next
    case (Inr_Inr_Inr a b c)
    with * have "(a,b) \<in> r'" "(b,c) \<in> r'" unfolding osum_def by auto
    with TRANS' have "(a,c) \<in> r'" unfolding trans_def by blast
    with Inr_Inr_Inr show ?thesis unfolding osum_def by auto
  qed (auto simp: osum_def)
qed

lemma osum_Preorder: "\<lbrakk>Preorder r; Preorder r'\<rbrakk> \<Longrightarrow> Preorder (r +o r')"
  unfolding preorder_on_def using osum_Refl osum_trans by blast

lemma osum_antisym: "\<lbrakk>antisym r; antisym r'\<rbrakk> \<Longrightarrow> antisym (r +o r')"
  unfolding antisym_def osum_def by auto

lemma osum_Partial_order: "\<lbrakk>Partial_order r; Partial_order r'\<rbrakk> \<Longrightarrow> Partial_order (r +o r')"
  unfolding partial_order_on_def using osum_Preorder osum_antisym by blast

lemma osum_Total: "\<lbrakk>Total r; Total r'\<rbrakk> \<Longrightarrow> Total (r +o r')"
  unfolding total_on_def Field_osum unfolding osum_def by blast

lemma osum_Linear_order: "\<lbrakk>Linear_order r; Linear_order r'\<rbrakk> \<Longrightarrow> Linear_order (r +o r')"
  unfolding linear_order_on_def using osum_Partial_order osum_Total by blast

lemma osum_wf:
  assumes WF: "wf r" and WF': "wf r'"
  shows "wf (r +o r')"
  unfolding wf_eq_minimal2 unfolding Field_osum
proof(intro allI impI, elim conjE)
  fix A assume *: "A \<subseteq> Inl ` Field r \<union> Inr ` Field r'" and **: "A \<noteq> {}"
  obtain B where B_def: "B = A Int Inl ` Field r" by blast
  show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> r +o r'"
  proof(cases "B = {}")
    case False
    hence "B \<noteq> {}" "B \<le> Inl ` Field r" using B_def by auto
    hence "Inl -` B \<noteq> {}" "Inl -` B \<le> Field r" unfolding vimage_def by auto
    then obtain a where 1: "a \<in> Inl -` B" and "\<forall>a1 \<in> Inl -` B. (a1, a) \<notin> r"
      using WF unfolding wf_eq_minimal2 by metis
    hence "\<forall>a1 \<in> A. (a1, Inl a) \<notin> r +o r'"
      unfolding osum_def using B_def ** by (auto simp: vimage_def Field_def)
    thus ?thesis using 1 unfolding B_def by auto
  next
    case True
    hence 1: "A \<le> Inr ` Field r'" using * B_def by auto
    with ** have "Inr -`A \<noteq> {}" "Inr -` A \<le> Field r'" unfolding vimage_def by auto
    with ** obtain a' where 2: "a' \<in> Inr -` A" and "\<forall>a1' \<in> Inr -` A. (a1',a') \<notin> r'"
      using WF' unfolding wf_eq_minimal2 by metis
    hence "\<forall>a1' \<in> A. (a1', Inr a') \<notin> r +o r'"
      unfolding osum_def using ** 1 by (auto simp: vimage_def Field_def)
    thus ?thesis using 2 by blast
  qed
qed

lemma osum_minus_Id:
  assumes r: "Total r" "\<not> (r \<le> Id)" and r': "Total r'" "\<not> (r' \<le> Id)"
  shows "(r +o r') - Id \<le> (r - Id) +o (r' - Id)"
  unfolding osum_def Total_Id_Field[OF r] Total_Id_Field[OF r'] by auto

lemma osum_minus_Id1:
  "r \<le> Id \<Longrightarrow> (r +o r') - Id \<le> (Inl ` Field r \<times> Inr ` Field r') \<union> (map_prod Inr Inr ` (r' - Id))"
  unfolding osum_def by auto

lemma osum_minus_Id2:
  "r' \<le> Id \<Longrightarrow> (r +o r') - Id \<le> (map_prod Inl Inl ` (r - Id)) \<union> (Inl ` Field r \<times> Inr ` Field r')"
  unfolding osum_def by auto

lemma osum_wf_Id:
  assumes TOT: "Total r" and TOT': "Total r'" and WF: "wf(r - Id)" and WF': "wf(r' - Id)"
  shows "wf ((r +o r') - Id)"
proof(cases "r \<le> Id \<or> r' \<le> Id")
  case False
  thus ?thesis
    using osum_minus_Id[of r r'] assms osum_wf[of "r - Id" "r' - Id"]
      wf_subset[of "(r - Id) +o (r' - Id)" "(r +o r') - Id"] by auto
next
  have 1: "wf (Inl ` Field r \<times> Inr ` Field r')" by (rule wf_Int_Times) auto
  case True
  thus ?thesis
  proof (elim disjE)
    assume "r \<subseteq> Id"
    thus "wf ((r +o r') - Id)"
      by (rule wf_subset[rotated, OF osum_minus_Id1 wf_Un[OF 1 wf_map_prod_image[OF WF']]]) auto
  next
    assume "r' \<subseteq> Id"
    thus "wf ((r +o r') - Id)"
      by (rule wf_subset[rotated, OF osum_minus_Id2 wf_Un[OF wf_map_prod_image[OF WF] 1]]) auto
  qed
qed

lemma osum_Well_order:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "Well_order (r +o r')"
  by (meson WELL WELL' osum_Linear_order osum_wf_Id well_order_on_def wo_rel.TOTAL wo_rel.intro)

lemma osum_embedL:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "embed r (r +o r') Inl"
proof -
  have 1: "Well_order (r +o r')" using assms by (auto simp add: osum_Well_order)
  moreover
  have "compat r (r +o r') Inl" unfolding compat_def osum_def by auto
  moreover
  have "ofilter (r +o r') (Inl ` Field r)"
    unfolding wo_rel.ofilter_def[unfolded wo_rel_def, OF 1] Field_osum under_def
    unfolding osum_def Field_def by auto
  ultimately show ?thesis using assms by (auto simp add: embed_iff_compat_inj_on_ofilter)
qed

corollary osum_ordLeqL:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "r \<le>o r +o r'"
  using assms osum_embedL osum_Well_order unfolding ordLeq_def by blast

lemma dir_image_alt: "dir_image r f = map_prod f f ` r"
  unfolding dir_image_def map_prod_def by auto

lemma map_prod_ordIso: "\<lbrakk>Well_order r; inj_on f (Field r)\<rbrakk> \<Longrightarrow> map_prod f f ` r =o r"
  by (metis dir_image_alt dir_image_ordIso ordIso_symmetric)

definition oprod :: "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel"  (infixr \<open>*o\<close> 80)
  where "r *o r' = {((x1, y1), (x2, y2)).
  (((y1, y2) \<in> r' - Id \<and> x1 \<in> Field r \<and> x2 \<in> Field r) \<or>
   ((y1, y2) \<in> Restr Id (Field r') \<and> (x1, x2) \<in> r))}"

lemma Field_oprod: "Field (r *o r') = Field r \<times> Field r'"
  unfolding oprod_def Field_def by auto blast+

lemma oprod_Refl:"\<lbrakk>Refl r; Refl r'\<rbrakk> \<Longrightarrow> Refl (r *o r')"
  unfolding refl_on_def Field_oprod unfolding oprod_def by auto

lemma oprod_trans:
  assumes "trans r" "trans r'" "antisym r" "antisym r'"
  shows "trans (r *o r')"
  using assms by (clarsimp simp: trans_def antisym_def oprod_def) (metis FieldI1 FieldI2)

lemma oprod_Preorder: "\<lbrakk>Preorder r; Preorder r'; antisym r; antisym r'\<rbrakk> \<Longrightarrow> Preorder (r *o r')"
  unfolding preorder_on_def using oprod_Refl oprod_trans by blast

lemma oprod_antisym: "\<lbrakk>antisym r; antisym r'\<rbrakk> \<Longrightarrow> antisym (r *o r')"
  unfolding antisym_def oprod_def by auto

lemma oprod_Partial_order: "\<lbrakk>Partial_order r; Partial_order r'\<rbrakk> \<Longrightarrow> Partial_order (r *o r')"
  unfolding partial_order_on_def using oprod_Preorder oprod_antisym by blast

lemma oprod_Total: "\<lbrakk>Total r; Total r'\<rbrakk> \<Longrightarrow> Total (r *o r')"
  unfolding total_on_def Field_oprod unfolding oprod_def by auto

lemma oprod_Linear_order: "\<lbrakk>Linear_order r; Linear_order r'\<rbrakk> \<Longrightarrow> Linear_order (r *o r')"
  unfolding linear_order_on_def using oprod_Partial_order oprod_Total by blast

lemma oprod_wf:
  assumes WF: "wf r" and WF': "wf r'"
  shows "wf (r *o r')"
  unfolding wf_eq_minimal2 unfolding Field_oprod
proof(intro allI impI, elim conjE)
  fix A assume *: "A \<subseteq> Field r \<times> Field r'" and **: "A \<noteq> {}"
  then obtain y where y: "y \<in> snd ` A" "\<forall>y'\<in>snd ` A. (y', y) \<notin> r'"
    using spec[OF WF'[unfolded wf_eq_minimal2], of "snd ` A"] by auto
  let ?A = "fst ` A \<inter> {x. (x, y) \<in> A}"
  from * y have "?A \<noteq> {}" "?A \<subseteq> Field r" by auto
  then obtain x where x: "x \<in> ?A" and "\<forall>x'\<in> ?A. (x', x) \<notin> r"
    using spec[OF WF[unfolded wf_eq_minimal2], of "?A"] by auto
  with y have "\<forall>a'\<in>A. (a', (x, y)) \<notin> r *o r'"
    unfolding oprod_def mem_Collect_eq split_beta fst_conv snd_conv Id_def by auto
  moreover from x have "(x, y) \<in> A" by auto
  ultimately show "\<exists>a\<in>A. \<forall>a'\<in>A. (a', a) \<notin> r *o r'" by blast
qed

lemma oprod_minus_Id:
  assumes r: "Total r" "\<not> (r \<le> Id)" and r': "Total r'" "\<not> (r' \<le> Id)"
  shows "(r *o r') - Id \<le> (r - Id) *o (r' - Id)"
  unfolding oprod_def Total_Id_Field[OF r] Total_Id_Field[OF r'] by auto

lemma oprod_minus_Id1:
  "r \<le> Id \<Longrightarrow> r *o r' - Id \<le> {((x,y1), (x,y2)). x \<in> Field r \<and> (y1, y2) \<in> (r' - Id)}"
  unfolding oprod_def by auto

lemma wf_extend_oprod1:
  assumes "wf r"
  shows "wf {((x,y1), (x,y2)) . x \<in> A \<and> (y1, y2) \<in> r}"
proof (unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix B
  assume *: "B \<subseteq> Field {((x,y1), (x,y2)) . x \<in> A \<and> (y1, y2) \<in> r}" and "B \<noteq> {}"
  from image_mono[OF *, of snd] have "snd ` B \<subseteq> Field r" unfolding Field_def by force
  with \<open>B \<noteq> {}\<close> obtain x where x: "x \<in> snd ` B" "\<forall>x'\<in>snd ` B. (x', x) \<notin> r"
    using spec[OF assms[unfolded wf_eq_minimal2], of "snd ` B"] by auto
  then obtain a where "(a, x) \<in> B" by auto
  moreover
  from * x have "\<forall>a'\<in>B. (a', (a, x)) \<notin> {((x,y1), (x,y2)) . x \<in> A \<and> (y1, y2) \<in> r}" by auto
  ultimately show "\<exists>ax\<in>B. \<forall>a'\<in>B. (a', ax) \<notin> {((x,y1), (x,y2)) . x \<in> A \<and> (y1, y2) \<in> r}" by blast
qed

lemma oprod_minus_Id2:
  "r' \<le> Id \<Longrightarrow> r *o r' - Id \<le> {((x1,y), (x2,y)). (x1, x2) \<in> (r - Id) \<and> y \<in> Field r'}"
  unfolding oprod_def by auto

lemma wf_extend_oprod2:
  assumes "wf r"
  shows "wf {((x1,y), (x2,y)) . (x1, x2) \<in> r \<and> y \<in> A}"
proof (unfold wf_eq_minimal2, intro allI impI, elim conjE)
  fix B
  assume *: "B \<subseteq> Field {((x1, y), (x2, y)). (x1, x2) \<in> r \<and> y \<in> A}" and "B \<noteq> {}"
  from image_mono[OF *, of fst] have "fst ` B \<subseteq> Field r" unfolding Field_def by force
  with \<open>B \<noteq> {}\<close> obtain x where x: "x \<in> fst ` B" "\<forall>x'\<in>fst ` B. (x', x) \<notin> r"
    using spec[OF assms[unfolded wf_eq_minimal2], of "fst ` B"] by auto
  then obtain a where "(x, a) \<in> B" by auto
  moreover
  from * x have "\<forall>a'\<in>B. (a', (x, a)) \<notin> {((x1, y), x2, y). (x1, x2) \<in> r \<and> y \<in> A}" by auto
  ultimately show "\<exists>xa\<in>B. \<forall>a'\<in>B. (a', xa) \<notin> {((x1, y), x2, y). (x1, x2) \<in> r \<and> y \<in> A}" by blast
qed

lemma oprod_wf_Id:
  assumes TOT: "Total r" and TOT': "Total r'" and WF: "wf(r - Id)" and WF': "wf(r' - Id)"
  shows "wf ((r *o r') - Id)"
proof(cases "r \<le> Id \<or> r' \<le> Id")
  case False
  thus ?thesis
    by (meson TOT TOT' WF WF' oprod_minus_Id oprod_wf wf_subset)
next
  case True
  thus ?thesis using wf_subset[OF wf_extend_oprod1[OF WF'] oprod_minus_Id1]
      wf_subset[OF wf_extend_oprod2[OF WF] oprod_minus_Id2] by auto
qed

lemma oprod_Well_order:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "Well_order (r *o r')"
  by (meson WELL WELL' linear_order_on_def oprod_Linear_order oprod_wf_Id well_order_on_def)

lemma oprod_embed:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and "r' \<noteq> {}"
  shows "embed r (r *o r') (\<lambda>x. (x, minim r' (Field r')))" (is "embed _ _ ?f")
proof -
  from assms(3) have r': "Field r' \<noteq> {}" unfolding Field_def by auto
  have minim[simp]: "minim r' (Field r') \<in> Field r'"
    using wo_rel.minim_inField[unfolded wo_rel_def, OF WELL' _ r'] by auto
  { fix b
    assume b: "(b, minim r' (Field r')) \<in> r'"
    hence "b \<in> Field r'" unfolding Field_def by auto
    hence "(minim r' (Field r'), b) \<in> r'"
      using wo_rel.minim_least[unfolded wo_rel_def, OF WELL' subset_refl] r' by auto
    with b have "b = minim r' (Field r')"
      by (metis WELL' antisym_def linear_order_on_def partial_order_on_def well_order_on_def)
  } note * = this
  have 1: "Well_order (r *o r')" using assms by (auto simp add: oprod_Well_order)
  moreover
  from r' have "compat r (r *o r') ?f"  unfolding compat_def oprod_def by auto
  moreover
  from * have "ofilter (r *o r') (?f ` Field r)"
    unfolding wo_rel.ofilter_def[unfolded wo_rel_def, OF 1] Field_oprod under_def
    unfolding oprod_def by auto (auto simp: image_iff Field_def)
  moreover have "inj_on ?f (Field r)" unfolding inj_on_def by auto
  ultimately show ?thesis using assms by (auto simp add: embed_iff_compat_inj_on_ofilter)
qed

corollary oprod_ordLeq: "\<lbrakk>Well_order r; Well_order r'; r' \<noteq> {}\<rbrakk> \<Longrightarrow> r \<le>o r *o r'"
  using oprod_embed oprod_Well_order unfolding ordLeq_def by blast

definition "support z A f = {x \<in> A. f x \<noteq> z}"

lemma support_Un[simp]: "support z (A \<union> B) f = support z A f \<union> support z B f"
  unfolding support_def by auto

lemma support_upd[simp]: "support z A (f(x := z)) = support z A f - {x}"
  unfolding support_def by auto

lemma support_upd_subset[simp]: "support z A (f(x := y)) \<subseteq> support z A f \<union> {x}"
  unfolding support_def by auto

lemma fun_unequal_in_support:
  assumes "f \<noteq> g" "f \<in> Func A B" "g \<in> Func A C"
  shows "(support z A f \<union> support z A g) \<inter> {a. f a \<noteq> g a} \<noteq> {}" 
  using assms by (simp add: Func_def support_def disjoint_iff fun_eq_iff) metis

definition fin_support where
  "fin_support z A = {f. finite (support z A f)}"

lemma finite_support: "f \<in> fin_support z A \<Longrightarrow> finite (support z A f)"
  unfolding support_def fin_support_def by auto

lemma fin_support_Field_osum:
  "f \<in> fin_support z (Inl ` A \<union> Inr ` B) \<longleftrightarrow>
  (f o Inl) \<in> fin_support z A \<and> (f o Inr) \<in> fin_support z B" (is "?L \<longleftrightarrow> ?R1 \<and> ?R2")
proof safe
  assume ?L
  from \<open>?L\<close> show ?R1 unfolding fin_support_def support_def
    by (fastforce simp: image_iff elim: finite_surj[of _ _ "case_sum id undefined"])
  from \<open>?L\<close> show ?R2 unfolding fin_support_def support_def
    by (fastforce simp: image_iff elim: finite_surj[of _ _ "case_sum undefined id"])
next
  assume ?R1 ?R2
  thus ?L unfolding fin_support_def support_Un
    by (auto simp: support_def elim: finite_surj[of _ _ Inl] finite_surj[of _ _ Inr])
qed

lemma Func_upd: "\<lbrakk>f \<in> Func A B; x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> f(x := y) \<in> Func A B"
  unfolding Func_def by auto

context wo_rel
begin

definition isMaxim :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "isMaxim A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. (a,b) \<in> r)"

definition maxim :: "'a set \<Rightarrow> 'a"
  where "maxim A \<equiv> THE b. isMaxim A b"

lemma isMaxim_unique[intro]: "\<lbrakk>isMaxim A x; isMaxim A y\<rbrakk> \<Longrightarrow> x = y"
  unfolding isMaxim_def using antisymD[OF ANTISYM, of x y] by auto

lemma maxim_isMaxim: "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> Field r\<rbrakk> \<Longrightarrow> isMaxim A (maxim A)"
  unfolding maxim_def
proof (rule theI', rule ex_ex1I[OF _ isMaxim_unique, rotated], assumption+,
    induct A rule: finite_induct)
  case (insert x A)
  thus ?case
  proof (cases "A = {}")
    case True
    moreover have "isMaxim {x} x" unfolding isMaxim_def using refl_onD[OF REFL] insert(5) by auto
    ultimately show ?thesis by blast
  next
    case False
    with insert(3,5) obtain y where "isMaxim A y" by blast
    with insert(2,5) have "if (y, x) \<in> r then isMaxim (insert x A) x else isMaxim (insert x A) y"
      unfolding isMaxim_def subset_eq by (metis insert_iff max2_def max2_equals1 max2_iff)
    thus ?thesis by metis
  qed
qed simp

lemma maxim_in: "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> Field r\<rbrakk> \<Longrightarrow> maxim A \<in> A"
  using maxim_isMaxim unfolding isMaxim_def by auto

lemma maxim_greatest: "\<lbrakk>finite A; x \<in> A; A \<subseteq> Field r\<rbrakk> \<Longrightarrow> (x, maxim A) \<in> r"
  using maxim_isMaxim unfolding isMaxim_def by auto

lemma isMaxim_zero: "isMaxim A zero \<Longrightarrow> A = {zero}"
  unfolding isMaxim_def by auto

lemma maxim_insert:
  assumes "finite A" "A \<noteq> {}" "A \<subseteq> Field r" "x \<in> Field r"
  shows "maxim (insert x A) = max2 x (maxim A)"
proof -
  from assms have *: "isMaxim (insert x A) (maxim (insert x A))" "isMaxim A (maxim A)"
    using maxim_isMaxim by auto
  show ?thesis
  proof (cases "(x, maxim A) \<in> r")
    case True
    with *(2) have "isMaxim (insert x A) (maxim A)"
      by (simp add: isMaxim_def)
    with *(1) True show ?thesis 
      unfolding max2_def by (metis isMaxim_unique)
  next
    case False
    hence "(maxim A, x) \<in> r" by (metis *(2) assms(3,4) in_mono in_notinI isMaxim_def)
    with *(2) assms(4) have "isMaxim (insert x A) x" unfolding isMaxim_def
      using transD[OF TRANS, of _ "maxim A" x] refl_onD[OF REFL, of x] by blast
    with *(1) False show ?thesis unfolding max2_def by (metis isMaxim_unique)
  qed
qed

lemma maxim_Un:
  assumes "finite A" "A \<noteq> {}" "A \<subseteq> Field r" "finite B" "B \<noteq> {}" "B \<subseteq> Field r"
  shows   "maxim (A \<union> B) = max2 (maxim A) (maxim B)"
proof -
  from assms have *: "isMaxim (A \<union> B) (maxim (A \<union> B))" "isMaxim A (maxim A)" "isMaxim B (maxim B)"
    using maxim_isMaxim by auto
  show ?thesis
  proof (cases "(maxim A, maxim B) \<in> r")
    case True
    with *(2,3) have "isMaxim (A \<union> B) (maxim B)" unfolding isMaxim_def
      using transD[OF TRANS, of _ "maxim A" "maxim B"] by blast
    with *(1) True show ?thesis unfolding max2_def by (metis isMaxim_unique)
  next
    case False
    hence "(maxim B, maxim A) \<in> r" by (metis *(2,3) assms(3,6) in_mono in_notinI isMaxim_def)
    with *(2,3) have "isMaxim (A \<union> B) (maxim A)"
      by (metis "*"(1) False Un_iff isMaxim_def isMaxim_unique)
    with *(1) False show ?thesis unfolding max2_def by (metis isMaxim_unique)
  qed
qed

lemma maxim_insert_zero:
  assumes "finite A" "A \<noteq> {}" "A \<subseteq> Field r"
  shows "maxim (insert zero A) = maxim A"
  using assms finite.cases in_mono max2_def maxim_in maxim_insert subset_empty zero_in_Field zero_smallest by fastforce

lemma maxim_equality: "isMaxim A x \<Longrightarrow> maxim A = x"
  unfolding maxim_def by (rule the_equality) auto

lemma maxim_singleton:
  "x \<in> Field r \<Longrightarrow> maxim {x} = x"
  using refl_onD[OF REFL] by (intro maxim_equality) (simp add: isMaxim_def)

lemma maxim_Int: "\<lbrakk>finite A; A \<noteq> {}; A \<subseteq> Field r; maxim A \<in> B\<rbrakk> \<Longrightarrow> maxim (A \<inter> B) = maxim A"
  by (rule maxim_equality) (auto simp: isMaxim_def intro: maxim_in maxim_greatest)

lemma maxim_mono: "\<lbrakk>X \<subseteq> Y; finite Y; X \<noteq> {}; Y \<subseteq> Field r\<rbrakk> \<Longrightarrow> (maxim X, maxim Y) \<in> r"
  using maxim_in[OF finite_subset, of X Y] by (auto intro: maxim_greatest)

definition "max_fun_diff f g \<equiv> maxim ({a \<in> Field r. f a \<noteq> g a})"

lemma max_fun_diff_commute: "max_fun_diff f g = max_fun_diff g f"
  unfolding max_fun_diff_def by metis

lemma zero_under: "x \<in> Field r \<Longrightarrow> zero \<in> under x"
  unfolding under_def by (auto intro: zero_smallest)

end

definition "FinFunc r s = Func (Field s) (Field r) \<inter> fin_support (zero r) (Field s)"

lemma FinFuncD: "\<lbrakk>f \<in> FinFunc r s; x \<in> Field s\<rbrakk> \<Longrightarrow> f x \<in> Field r"
  unfolding FinFunc_def Func_def by (fastforce split: option.splits)

locale wo_rel2 =
  fixes r s
  assumes rWELL: "Well_order r"
    and     sWELL: "Well_order s"
begin

interpretation r: wo_rel r by unfold_locales (rule rWELL)
interpretation s: wo_rel s by unfold_locales (rule sWELL)

abbreviation "SUPP \<equiv> support r.zero (Field s)"
abbreviation "FINFUNC \<equiv> FinFunc r s"
lemmas FINFUNCD = FinFuncD[of _ r s]

lemma fun_diff_alt: "{a \<in> Field s. f a \<noteq> g a} = (SUPP f \<union> SUPP g) \<inter> {a. f a \<noteq> g a}"
  by (auto simp: support_def)

lemma max_fun_diff_alt:
  "s.max_fun_diff f g = s.maxim ((SUPP f \<union> SUPP g) \<inter> {a. f a \<noteq> g a})"
  unfolding s.max_fun_diff_def fun_diff_alt ..

lemma isMaxim_max_fun_diff: "\<lbrakk>f \<noteq> g; f \<in> FINFUNC; g \<in> FINFUNC\<rbrakk> \<Longrightarrow>
  s.isMaxim {a \<in> Field s. f a \<noteq> g a} (s.max_fun_diff f g)"
  using fun_unequal_in_support[of f g] unfolding max_fun_diff_alt fun_diff_alt fun_eq_iff
  by (intro s.maxim_isMaxim) (auto simp: FinFunc_def fin_support_def support_def)

lemma max_fun_diff_in: "\<lbrakk>f \<noteq> g; f \<in> FINFUNC; g \<in> FINFUNC\<rbrakk> \<Longrightarrow>
  s.max_fun_diff f g \<in> {a \<in> Field s. f a \<noteq> g a}"
  using isMaxim_max_fun_diff unfolding s.isMaxim_def by blast

lemma max_fun_diff_max: "\<lbrakk>f \<noteq> g; f \<in> FINFUNC; g \<in> FINFUNC; x \<in> {a \<in> Field s. f a \<noteq> g a}\<rbrakk> \<Longrightarrow>
  (x, s.max_fun_diff f g) \<in> s"
  using isMaxim_max_fun_diff unfolding s.isMaxim_def by blast

lemma max_fun_diff:
  "\<lbrakk>f \<noteq> g; f \<in> FINFUNC; g \<in> FINFUNC\<rbrakk> \<Longrightarrow>
  (\<exists>a b. a \<noteq> b \<and> a \<in> Field r \<and> b \<in> Field r \<and>
     f (s.max_fun_diff f g) = a \<and> g (s.max_fun_diff f g) = b)"
  using isMaxim_max_fun_diff[of f g] unfolding s.isMaxim_def FinFunc_def Func_def by auto

lemma max_fun_diff_le_eq:
  "\<lbrakk>(s.max_fun_diff f g, x) \<in> s; f \<noteq> g; f \<in> FINFUNC; g \<in> FINFUNC; x \<noteq> s.max_fun_diff f g\<rbrakk> \<Longrightarrow>
  f x = g x"
  using max_fun_diff_max[of f g x] antisymD[OF s.ANTISYM, of "s.max_fun_diff f g" x]
  by (auto simp: Field_def)

lemma max_fun_diff_max2:
  assumes ineq: "s.max_fun_diff f g = s.max_fun_diff g h \<longrightarrow>
    f (s.max_fun_diff f g) \<noteq> h (s.max_fun_diff g h)" and
    fg: "f \<noteq> g" and gh: "g \<noteq> h" and fh: "f \<noteq> h" and
    f: "f \<in> FINFUNC" and g: "g \<in> FINFUNC" and h: "h \<in> FINFUNC"
  shows "s.max_fun_diff f h = s.max2 (s.max_fun_diff f g) (s.max_fun_diff g h)"
    (is "?fh = s.max2 ?fg ?gh")
proof (cases "?fg = ?gh")
  case True
  with ineq have "f ?fg \<noteq> h ?fg" by simp
  moreover
  { fix x assume x: "x \<in> {a \<in> Field s. f a \<noteq> h a}"
    hence "(x, ?fg) \<in> s"
    proof (cases "x = ?fg")
      case False show ?thesis
        by (metis (mono_tags, lifting) True assms(5-7) max_fun_diff_max mem_Collect_eq x)
    qed (simp add: refl_onD[OF s.REFL])
  }
  ultimately have "s.isMaxim {a \<in> Field s. f a \<noteq> h a} ?fg"
    unfolding s.isMaxim_def using max_fun_diff_in[OF fg f g] by simp
  hence "?fh = ?fg" using isMaxim_max_fun_diff[OF fh f h] by blast
  thus ?thesis unfolding True s.max2_def by simp
next
  case False note * = this
  show ?thesis
  proof (cases "(?fg, ?gh) \<in> s")
    case True
    hence *: "f ?gh = g ?gh" by (rule max_fun_diff_le_eq[OF _ fg f g *[symmetric]])
    hence "s.isMaxim {a \<in> Field s. f a \<noteq> h a} ?gh" using isMaxim_max_fun_diff[OF gh g h]
        isMaxim_max_fun_diff[OF fg f g] transD[OF s.TRANS _ True]
      unfolding s.isMaxim_def by auto
    hence "?fh = ?gh" using isMaxim_max_fun_diff[OF fh f h] by blast
    thus ?thesis using True unfolding s.max2_def by simp
  next
    case False
    with max_fun_diff_in[OF fg f g] max_fun_diff_in[OF gh g h] have True: "(?gh, ?fg) \<in> s"
      by (blast intro: s.in_notinI)
    hence *: "g ?fg = h ?fg" by (rule max_fun_diff_le_eq[OF _ gh g h *])
    hence "s.isMaxim {a \<in> Field s. f a \<noteq> h a} ?fg" using isMaxim_max_fun_diff[OF gh g h]
        isMaxim_max_fun_diff[OF fg f g] True transD[OF s.TRANS, of _ _ ?fg]
      unfolding s.isMaxim_def by auto
    hence "?fh = ?fg" using isMaxim_max_fun_diff[OF fh f h] by blast
    thus ?thesis using False unfolding s.max2_def by simp
  qed
qed

definition oexp where
  "oexp = {(f, g) . f \<in> FINFUNC \<and> g \<in> FINFUNC \<and>
    ((let m = s.max_fun_diff f g in (f m, g m) \<in> r) \<or> f = g)}"

lemma Field_oexp: "Field oexp = FINFUNC"
  unfolding oexp_def FinFunc_def by (auto simp: Let_def Field_def)

lemma oexp_Refl: "Refl oexp"
  unfolding refl_on_def Field_oexp unfolding oexp_def by (auto simp: Let_def)

lemma oexp_trans: "trans oexp"
proof (unfold trans_def, safe)
  fix f g h :: "'b \<Rightarrow> 'a"
  let ?fg = "s.max_fun_diff f g"
    and ?gh = "s.max_fun_diff g h"
    and ?fh = "s.max_fun_diff f h"
  assume oexp: "(f, g) \<in> oexp" "(g, h) \<in> oexp"
  thus "(f, h) \<in> oexp"
  proof (cases "f = g \<or> g = h")
    case False
    with oexp have "f \<in> FINFUNC" "g \<in> FINFUNC" "h \<in> FINFUNC"
      "(f ?fg, g ?fg) \<in> r" "(g ?gh, h ?gh) \<in> r" unfolding oexp_def Let_def by auto
    note * = this False
    show ?thesis
    proof (cases "f \<noteq> h")
      case True
      show ?thesis
      proof (cases "?fg = ?gh \<longrightarrow> f ?fg \<noteq> h ?gh")
        case True
        show ?thesis using max_fun_diff_max2[of f g h, OF True] * \<open>f \<noteq> h\<close> max_fun_diff_in
            r.max2_iff[OF FINFUNCD FINFUNCD] r.max2_equals1[OF FINFUNCD FINFUNCD] max_fun_diff_le_eq
            s.in_notinI[OF disjI1] unfolding oexp_def Let_def s.max2_def mem_Collect_eq by safe metis
      next
        case False with * show ?thesis unfolding oexp_def Let_def
          using antisymD[OF r.ANTISYM, of "g ?gh" "h ?gh"] max_fun_diff_in[of g h] by auto
      qed
    qed (auto simp: oexp_def *(3))
  qed auto
qed

lemma oexp_Preorder: "Preorder oexp"
  unfolding preorder_on_def using oexp_Refl oexp_trans by blast

lemma oexp_antisym: "antisym oexp"
proof (unfold antisym_def, safe, rule ccontr)
  fix f g assume "(f, g) \<in> oexp" "(g, f) \<in> oexp" "g \<noteq> f"
  thus False using refl_onD[OF r.REFL FINFUNCD] max_fun_diff_in unfolding oexp_def Let_def
    by (auto dest!: antisymD[OF r.ANTISYM] simp: s.max_fun_diff_commute)
qed

lemma oexp_Partial_order: "Partial_order oexp"
  unfolding partial_order_on_def using oexp_Preorder oexp_antisym by blast

lemma oexp_Total: "Total oexp"
  unfolding total_on_def Field_oexp unfolding oexp_def using FINFUNCD max_fun_diff_in
  by (auto simp: Let_def s.max_fun_diff_commute intro!: r.in_notinI)

lemma oexp_Linear_order: "Linear_order oexp"
  unfolding linear_order_on_def using oexp_Partial_order oexp_Total by blast

definition "const = (\<lambda>x. if x \<in> Field s then r.zero else undefined)"

lemma const_in[simp]: "x \<in> Field s \<Longrightarrow> const x = r.zero"
  unfolding const_def by auto

lemma const_notin[simp]: "x \<notin> Field s \<Longrightarrow> const x = undefined"
  unfolding const_def by auto

lemma const_Int_Field[simp]: "Field s \<inter> - {x. const x = r.zero} = {}"
  by auto

lemma const_FINFUNC[simp]: "Field r \<noteq> {} \<Longrightarrow> const \<in> FINFUNC"
  unfolding FinFunc_def Func_def fin_support_def support_def const_def Int_iff mem_Collect_eq
  using r.zero_in_Field by (metis (lifting) Collect_empty_eq finite.emptyI)

lemma const_least:
  assumes "Field r \<noteq> {}" "f \<in> FINFUNC"
  shows "(const, f) \<in> oexp"
  using assms const_FINFUNC max_fun_diff max_fun_diff_in oexp_def by fastforce

lemma support_not_const:
  assumes "F \<subseteq> FINFUNC" and "const \<notin> F"
  shows "\<forall>f \<in> F. finite (SUPP f) \<and> SUPP f \<noteq> {} \<and> SUPP f \<subseteq> Field s"
proof (intro ballI conjI)
  fix f assume "f \<in> F"
  thus "finite (SUPP f)" "SUPP f \<subseteq> Field s"
    using assms(1) unfolding FinFunc_def fin_support_def support_def by auto
  show "SUPP f \<noteq> {}"
  proof (rule ccontr, unfold not_not)
    assume "SUPP f = {}"
    moreover from \<open>f \<in> F\<close> assms(1) have "f \<in> FINFUNC" by blast
    ultimately have "f = const"
      by (auto simp: fun_eq_iff support_def FinFunc_def Func_def const_def)
    with assms(2) \<open>f \<in> F\<close> show False by blast
  qed
qed

lemma maxim_isMaxim_support:
  assumes "F \<subseteq> FINFUNC" and "const \<notin> F"
  shows "\<forall>f \<in> F. s.isMaxim (SUPP f) (s.maxim (SUPP f))"
  using assms s.maxim_isMaxim support_not_const by force

lemma oexp_empty2: "Field s = {} \<Longrightarrow> oexp = {(\<lambda>x. undefined, \<lambda>x. undefined)}"
  unfolding oexp_def FinFunc_def fin_support_def support_def by auto

lemma oexp_empty: "\<lbrakk>Field r = {}; Field s \<noteq> {}\<rbrakk> \<Longrightarrow> oexp = {}"
  using FINFUNCD oexp_def by auto

lemma fun_upd_FINFUNC: "\<lbrakk>f \<in> FINFUNC; x \<in> Field s; y \<in> Field r\<rbrakk> \<Longrightarrow> f(x := y) \<in> FINFUNC"
  unfolding FinFunc_def Func_def fin_support_def
  by (auto intro: finite_subset[OF support_upd_subset])

lemma fun_upd_same_oexp:
  assumes "(f, g) \<in> oexp" "f x = g x" "x \<in> Field s" "y \<in> Field r"
  shows   "(f(x := y), g(x := y)) \<in> oexp"
proof -
  from assms(1) fun_upd_FINFUNC[OF _ assms(3,4)] have fg: "f(x := y) \<in> FINFUNC" "g(x := y) \<in> FINFUNC"
    unfolding oexp_def by auto
  moreover from assms(2) have "s.max_fun_diff (f(x := y)) (g(x := y)) = s.max_fun_diff f g"
    unfolding s.max_fun_diff_def by auto metis
  ultimately show ?thesis using assms refl_onD[OF r.REFL] unfolding oexp_def Let_def by auto
qed

lemma fun_upd_smaller_oexp:
  assumes "f \<in> FINFUNC" "x \<in> Field s" "y \<in> Field r"  "(y, f x) \<in> r"
  shows   "(f(x := y), f) \<in> oexp"
  using assms fun_upd_FINFUNC[OF assms(1-3)] s.maxim_singleton[of "x"]
  unfolding oexp_def FinFunc_def Let_def fin_support_def s.max_fun_diff_def by (auto simp: fun_eq_iff)

lemma oexp_wf_Id: "wf (oexp - Id)"
proof (cases "Field r = {} \<or> Field s = {}")
  case True thus ?thesis using oexp_empty oexp_empty2 by fastforce
next
  case False
  hence Fields: "Field s \<noteq> {}" "Field r \<noteq> {}" by simp_all
  hence [simp]: "r.zero \<in> Field r" by (intro r.zero_in_Field)
  have const[simp]: "\<And>F. \<lbrakk>const \<in> F; F \<subseteq> FINFUNC\<rbrakk> \<Longrightarrow> \<exists>f0\<in>F. \<forall>f\<in>F. (f0, f) \<in> oexp"
    using const_least[OF Fields(2)] by auto
  show ?thesis
    unfolding Linear_order_wf_diff_Id[OF oexp_Linear_order] Field_oexp
  proof (intro allI impI)
    fix A assume A: "A \<subseteq> FINFUNC" "A \<noteq> {}"
    { fix y F
      have "F \<subseteq> FINFUNC \<and> (\<exists>f \<in> F. y = s.maxim (SUPP f)) \<longrightarrow>
        (\<exists>f0 \<in> F. \<forall>f \<in> F. (f0, f) \<in> oexp)" (is "?P F y")
      proof (induct y arbitrary: F rule: s.well_order_induct)
        case (1 y)
        show ?case
        proof (intro impI, elim conjE bexE)
          fix f assume F: "F \<subseteq> FINFUNC" "f \<in> F" "y = s.maxim (SUPP f)"
          thus "\<exists>f0\<in>F. \<forall>f\<in>F. (f0, f) \<in> oexp"
          proof (cases "const \<in> F")
            case False
            with F have maxF: "\<forall>f \<in> F. s.isMaxim (SUPP f) (s.maxim (SUPP f))"
              and SUPPF: "\<forall>f \<in> F. finite (SUPP f) \<and> SUPP f \<noteq> {} \<and> SUPP f \<subseteq> Field s"
              using maxim_isMaxim_support support_not_const by auto
            define z where "z = s.minim {s.maxim (SUPP f) | f. f \<in> F}"
            from F SUPPF maxF have zmin: "s.isMinim {s.maxim (SUPP f) | f. f \<in> F} z"
              unfolding z_def by (intro s.minim_isMinim) (auto simp: s.isMaxim_def)
            with F have zy: "(z, y) \<in> s" unfolding s.isMinim_def by auto
            hence zField: "z \<in> Field s" unfolding Field_def by auto
            define x0 where "x0 = r.minim {f z | f. f \<in> F \<and> z = s.maxim (SUPP f)}"
            from F(1,2) maxF(1) SUPPF zmin
            have x0min: "r.isMinim {f z | f. f \<in> F \<and> z = s.maxim (SUPP f)} x0"
              unfolding x0_def s.isMaxim_def s.isMinim_def
              by (blast intro!: r.minim_isMinim FinFuncD[of _ r s])
            with maxF(1) SUPPF F(1) have x0Field: "x0 \<in> Field r"
              unfolding r.isMinim_def s.isMaxim_def by (auto intro!: FINFUNCD)
            from x0min maxF(1) SUPPF F(1) have x0notzero: "x0 \<noteq> r.zero"
              unfolding r.isMinim_def s.isMaxim_def FinFunc_def Func_def support_def
              by fastforce
            define G where "G = {f(z := r.zero) | f. f \<in> F \<and> z = s.maxim (SUPP f) \<and> f z = x0}"
            from zmin x0min have "G \<noteq> {}" unfolding G_def z_def s.isMinim_def r.isMinim_def by blast
            have GF: "G \<subseteq> (\<lambda>f. f(z := r.zero)) ` F" unfolding G_def by auto
            have "G \<subseteq> fin_support r.zero (Field s)"
              unfolding FinFunc_def fin_support_def
              using F(1) FinFunc_def G_def fin_support_def by fastforce
            moreover from F GF zField have "G \<subseteq> Func (Field s) (Field r)"
              using Func_upd[of _ "Field s" "Field r" z r.zero] unfolding FinFunc_def by auto
            ultimately have G: "G \<subseteq> FINFUNC" unfolding FinFunc_def by blast
            hence "\<exists>g0\<in>G. \<forall>g\<in>G. (g0, g) \<in> oexp"
            proof (cases "const \<in> G")
              case False
              with G have maxG: "\<forall>g \<in> G. s.isMaxim (SUPP g) (s.maxim (SUPP g))"
                and SUPPG: "\<forall>g \<in> G. finite (SUPP g) \<and> SUPP g \<noteq> {} \<and> SUPP g \<subseteq> Field s"
                using maxim_isMaxim_support support_not_const by auto
              define y' where "y' = s.minim {s.maxim (SUPP f) | f. f \<in> G}"
              from G SUPPG maxG \<open>G \<noteq> {}\<close> have y'min: "s.isMinim {s.maxim (SUPP f) | f. f \<in> G} y'"
                unfolding y'_def by (intro s.minim_isMinim) (auto simp: s.isMaxim_def)
              moreover
              have "\<forall>g \<in> G. z \<notin> SUPP g" unfolding support_def G_def by auto
              moreover
              { fix g assume g: "g \<in> G"
                then obtain f where "f \<in> F" "g = f(z := r.zero)" and z: "z = s.maxim (SUPP f)"
                  unfolding G_def by auto
                with SUPPF bspec[OF SUPPG g] have "(s.maxim (SUPP g), z) \<in> s"
                  unfolding z by (intro s.maxim_mono) auto
              }
              moreover from y'min have "\<And>g. g \<in> G \<Longrightarrow> (y', s.maxim (SUPP g)) \<in> s"
                unfolding s.isMinim_def by auto
              ultimately have "y' \<noteq> z" "(y', z) \<in> s" using maxG
                unfolding s.isMinim_def s.isMaxim_def by auto
              with zy have "y' \<noteq> y" "(y', y) \<in> s" using antisymD[OF s.ANTISYM] transD[OF s.TRANS]
                by blast+
              moreover from \<open>G \<noteq> {}\<close> have "\<exists>g \<in> G. y' = wo_rel.maxim s (SUPP g)" using y'min
                by (auto simp: G_def s.isMinim_def)
              ultimately show ?thesis using mp[OF spec[OF mp[OF spec[OF 1]]], of y' G] G by auto
            qed simp
            then obtain g0 where g0: "g0 \<in> G" "\<forall>g \<in> G. (g0, g) \<in> oexp" by blast
            hence g0z: "g0 z = r.zero" unfolding G_def by auto
            define f0 where "f0 = g0(z := x0)"
            with x0notzero zField have SUPP: "SUPP f0 = SUPP g0 \<union> {z}" unfolding support_def by auto
            from g0z have f0z: "f0(z := r.zero) = g0" unfolding f0_def fun_upd_upd by auto
            have f0: "f0 \<in> F" using x0min g0(1)
                Func_elim[OF subsetD[OF subset_trans[OF F(1)[unfolded FinFunc_def] Int_lower1]] zField]
              unfolding f0_def r.isMinim_def G_def by (force simp: fun_upd_idem)
            from g0(1) maxF(1) have maxf0: "s.maxim (SUPP f0) = z" unfolding SUPP G_def
              by (intro s.maxim_equality) (auto simp: s.isMaxim_def)
            show ?thesis
            proof (intro bexI[OF _ f0] ballI)
              fix f assume f: "f \<in> F"
              show "(f0, f) \<in> oexp"
              proof (cases "f0 = f")
                case True thus ?thesis by (metis F(1) Field_oexp f0 in_mono oexp_Refl refl_onD)
              next
                case False
                thus ?thesis
                proof (cases "s.maxim (SUPP f) = z \<and> f z = x0")
                  case True
                  with f have "f(z := r.zero) \<in> G" unfolding G_def by blast
                  with g0(2) f0z have "(f0(z := r.zero), f(z := r.zero)) \<in> oexp" by auto
                  hence oexp: "(f0(z := r.zero, z := x0), f(z := r.zero, z := x0)) \<in> oexp"
                    by (elim fun_upd_same_oexp[OF _ _ zField x0Field]) simp
                  with f F(1) x0min True
                  have "(f(z := x0), f) \<in> oexp" unfolding G_def r.isMinim_def
                    by (intro fun_upd_smaller_oexp[OF _ zField x0Field]) auto
                  with oexp show ?thesis using transD[OF oexp_trans, of f0 "f(z := x0)" f]
                    unfolding f0_def by auto
                next
                  case False note notG = this
                  thus ?thesis
                  proof (cases "s.maxim (SUPP f) = z")
                    case True
                    with notG have "f0 z \<noteq> f z" unfolding f0_def by auto
                    hence "f0 z \<noteq> f z" by metis
                    with True maxf0 f0 f SUPPF have "s.max_fun_diff f0 f = z"
                      using s.maxim_Un[of "SUPP f0" "SUPP f", unfolded s.max2_def]
                      unfolding max_fun_diff_alt by (intro trans[OF s.maxim_Int]) auto
                    moreover
                    from x0min True f have "(x0, f z) \<in> r" unfolding r.isMinim_def by auto
                    ultimately show ?thesis using f f0 F(1) unfolding oexp_def f0_def by auto
                  next
                    case False
                    with notG have *: "(z, s.maxim (SUPP f)) \<in> s" "z \<noteq> s.maxim (SUPP f)"
                      using zmin f unfolding s.isMinim_def G_def by auto
                    have f0f: "f0 (s.maxim (SUPP f)) = r.zero"
                    proof (rule ccontr)
                      assume "f0 (s.maxim (SUPP f)) \<noteq> r.zero"
                      with f SUPPF maxF(1) have "s.maxim (SUPP f) \<in> SUPP f0"
                        unfolding support_def[of _ _ f0] s.isMaxim_def by auto
                      with SUPPF f0 have "(s.maxim (SUPP f), z) \<in> s" unfolding maxf0[symmetric]
                        by (auto intro: s.maxim_greatest)
                      with * antisymD[OF s.ANTISYM] show False by simp
                    qed
                    moreover
                    have "f (s.maxim (SUPP f)) \<noteq> r.zero"
                      using bspec[OF maxF(1) f, unfolded s.isMaxim_def] by (auto simp: support_def)
                    with f0f * f f0 maxf0 SUPPF
                    have "s.max_fun_diff f0 f = s.maxim (SUPP f0 \<union> SUPP f)"
                      unfolding max_fun_diff_alt using s.maxim_Un[of "SUPP f0" "SUPP f"]
                      by (intro s.maxim_Int) (auto simp: s.max2_def)
                    moreover have "s.maxim (SUPP f0 \<union> SUPP f) = s.maxim (SUPP f)"
                      using s.maxim_Un[of "SUPP f0" "SUPP f"] * maxf0 SUPPF f0 f
                      by (auto simp: s.max2_def)
                    ultimately show ?thesis using f f0 F(1) maxF(1) SUPPF unfolding oexp_def Let_def
                      by (fastforce simp: s.isMaxim_def intro!: r.zero_smallest FINFUNCD)
                  qed
                qed
              qed
            qed
          qed simp
        qed
      qed
    } 
    with A show "\<exists>a\<in>A. \<forall>a'\<in>A. (a, a') \<in> oexp"
      by blast
  qed
qed

lemma oexp_Well_order: "Well_order oexp"
  unfolding well_order_on_def using oexp_Linear_order oexp_wf_Id by blast

interpretation o: wo_rel oexp by unfold_locales (rule oexp_Well_order)

lemma zero_oexp: "Field r \<noteq> {} \<Longrightarrow> o.zero = const"
  by (metis Field_oexp const_FINFUNC const_least o.Field_ofilter o.equals_minim o.ofilter_def o.zero_def)

end

notation wo_rel2.oexp (infixl \<open>^o\<close> 90)
lemmas oexp_def = wo_rel2.oexp_def[unfolded wo_rel2_def, OF conjI]
lemmas oexp_Well_order = wo_rel2.oexp_Well_order[unfolded wo_rel2_def, OF conjI]
lemmas Field_oexp = wo_rel2.Field_oexp[unfolded wo_rel2_def, OF conjI]

definition "ozero = {}"

lemma ozero_Well_order[simp]: "Well_order ozero"
  unfolding ozero_def by simp

lemma ozero_ordIso[simp]: "ozero =o ozero"
  unfolding ozero_def ordIso_def iso_def[abs_def] embed_def bij_betw_def by auto

lemma Field_ozero[simp]: "Field ozero = {}"
  unfolding ozero_def by simp

lemma iso_ozero_empty[simp]: "r =o ozero = (r = {})"
  unfolding ozero_def ordIso_def iso_def[abs_def] embed_def bij_betw_def
  by (auto dest: well_order_on_domain)

lemma ozero_ordLeq:
  assumes "Well_order r"  shows "ozero \<le>o r"
  using assms unfolding ozero_def ordLeq_def embed_def[abs_def] under_def by auto

definition "oone = {((),())}"

lemma oone_Well_order[simp]: "Well_order oone"
  unfolding oone_def unfolding well_order_on_def linear_order_on_def partial_order_on_def
    preorder_on_def total_on_def refl_on_def trans_def antisym_def by auto

lemma Field_oone[simp]: "Field oone = {()}"
  unfolding oone_def by simp

lemma oone_ordIso: "oone =o {(x,x)}"
  unfolding ordIso_def oone_def well_order_on_def linear_order_on_def partial_order_on_def
    preorder_on_def total_on_def refl_on_def trans_def antisym_def
  by (auto simp: iso_def embed_def bij_betw_def under_def inj_on_def intro!: exI[of _ "\<lambda>_. x"])

lemma osum_ordLeqR: "Well_order r \<Longrightarrow> Well_order s \<Longrightarrow> s \<le>o r +o s"
  unfolding ordLeq_def2 underS_def
  by (auto intro!: exI[of _ Inr] osum_Well_order) (auto simp add: osum_def Field_def)

lemma osum_congL:
  assumes "r =o s" and t: "Well_order t"
  shows "r +o t =o s +o t" (is "?L =o ?R")
proof -
  from assms(1) obtain f where r: "Well_order r" and s: "Well_order s" and f: "iso r s f"
    unfolding ordIso_def by blast
  let ?f = "map_sum f id"
  from f have "inj_on ?f (Field ?L)"
    unfolding Field_osum iso_def bij_betw_def inj_on_def by fastforce
  with f have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_osum iso_def bij_betw_def image_image image_Un by auto
  moreover from f have "compat ?L ?R ?f"
    unfolding osum_def iso_iff3[OF r s] compat_def bij_betw_def
    by (auto simp: map_prod_imageI)
  ultimately have "iso ?L ?R ?f" by (subst iso_iff3) (auto intro: osum_Well_order r s t)
  thus ?thesis unfolding ordIso_def by (auto intro: osum_Well_order r s t)
qed

lemma osum_congR:
  assumes "r =o s" and t: "Well_order t"
  shows "t +o r =o t +o s" (is "?L =o ?R")
proof -
  from assms(1) obtain f where r: "Well_order r" and s: "Well_order s" and f: "iso r s f"
    unfolding ordIso_def by blast
  let ?f = "map_sum id f"
  from f have "inj_on ?f (Field ?L)"
    unfolding Field_osum iso_def bij_betw_def inj_on_def by fastforce
  with f have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_osum iso_def bij_betw_def image_image image_Un by auto
  moreover from f have "compat ?L ?R ?f"
    unfolding osum_def iso_iff3[OF r s] compat_def bij_betw_def
    by (auto simp: map_prod_imageI)
  ultimately have "iso ?L ?R ?f" by (subst iso_iff3) (auto intro: osum_Well_order r s t)
  thus ?thesis unfolding ordIso_def by (auto intro: osum_Well_order r s t)
qed

lemma osum_cong:
  assumes "t =o u" and "r =o s"
  shows "t +o r =o u +o s"
  using ordIso_transitive[OF osum_congL[OF assms(1)] osum_congR[OF assms(2)]]
    assms[unfolded ordIso_def] by auto

lemma Well_order_empty[simp]: "Well_order {}"
  unfolding Field_empty by (rule well_order_on_empty)

lemma well_order_on_singleton[simp]: "well_order_on {x} {(x, x)}"
  unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def total_on_def
    Field_def refl_on_def trans_def antisym_def by auto

lemma oexp_empty[simp]:
  assumes "Well_order r"
  shows "r ^o {} = {(\<lambda>x. undefined, \<lambda>x. undefined)}"
  unfolding oexp_def[OF assms Well_order_empty] FinFunc_def fin_support_def support_def by auto

lemma oexp_empty2[simp]:
  assumes "Well_order r" "r \<noteq> {}"
  shows "{} ^o r = {}"
proof -
  from assms(2) have "Field r \<noteq> {}" unfolding Field_def by auto
  thus ?thesis
    by (simp add: assms(1) wo_rel2.intro wo_rel2.oexp_empty)
qed

lemma oprod_zero[simp]: "{} *o r = {}" "r *o {} = {}"
  unfolding oprod_def by simp_all

lemma oprod_congL:
  assumes "r =o s" and t: "Well_order t"
  shows "r *o t =o s *o t" (is "?L =o ?R")
proof -
  from assms(1) obtain f where r: "Well_order r" and s: "Well_order s" and f: "iso r s f"
    unfolding ordIso_def by blast
  let ?f = "map_prod f id"
  from f have "inj_on ?f (Field ?L)"
    unfolding Field_oprod iso_def bij_betw_def inj_on_def by fastforce
  with f have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_oprod iso_def bij_betw_def by (auto intro!: map_prod_surj_on)
  moreover from f have "compat ?L ?R ?f"
    unfolding iso_iff3[OF r s] compat_def oprod_def bij_betw_def
    by (auto simp: map_prod_imageI)
  ultimately have "iso ?L ?R ?f" by (subst iso_iff3) (auto intro: oprod_Well_order r s t)
  thus ?thesis unfolding ordIso_def by (auto intro: oprod_Well_order r s t)
qed

lemma oprod_congR:
  assumes "r =o s" and t: "Well_order t"
  shows "t *o r =o t *o s" (is "?L =o ?R")
proof -
  from assms(1) obtain f where r: "Well_order r" and s: "Well_order s" and f: "iso r s f"
    unfolding ordIso_def by blast
  let ?f = "map_prod id f"
  from f have "inj_on ?f (Field ?L)"
    unfolding Field_oprod iso_def bij_betw_def inj_on_def by fastforce
  with f have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_oprod iso_def bij_betw_def by (auto intro!: map_prod_surj_on)
  moreover from f well_order_on_domain[OF r] have "compat ?L ?R ?f"
    unfolding iso_iff3[OF r s] compat_def oprod_def bij_betw_def
    by (auto simp: map_prod_imageI dest: inj_onD)
  ultimately have "iso ?L ?R ?f" by (subst iso_iff3) (auto intro: oprod_Well_order r s t)
  thus ?thesis unfolding ordIso_def by (auto intro: oprod_Well_order r s t)
qed

lemma oprod_cong:
  assumes "t =o u" and "r =o s"
  shows "t *o r =o u *o s"
  using ordIso_transitive[OF oprod_congL[OF assms(1)] oprod_congR[OF assms(2)]]
    assms[unfolded ordIso_def] by auto

lemma Field_singleton[simp]: "Field {(z,z)} = {z}"
  by (metis well_order_on_Field well_order_on_singleton)

lemma zero_singleton[simp]: "zero {(z,z)} = z"
  using wo_rel.zero_in_Field[unfolded wo_rel_def, of "{(z, z)}"] well_order_on_singleton[of z]
  by auto

lemma FinFunc_singleton: "FinFunc {(z,z)} s = {\<lambda>x. if x \<in> Field s then z else undefined}"
  unfolding FinFunc_def Func_def fin_support_def support_def
  by (auto simp: fun_eq_iff split: if_split_asm intro!: finite_subset[of _ "{}"])

lemma oone_ordIso_oexp:
  assumes "r =o oone" and s: "Well_order s"
  shows "r ^o s =o oone" (is "?L =o ?R")
proof -
  from \<open>r =o oone\<close> obtain f where *: "\<forall>x\<in>Field r. \<forall>y\<in>Field r. x = y" and "f ` Field r = {()}"
    and r: "Well_order r"
    unfolding ordIso_def oone_def by (auto simp add: iso_def [abs_def] bij_betw_def inj_on_def)
  then obtain x where "x \<in> Field r" by auto
  with * have Fr: "Field r = {x}" by auto
  interpret r: wo_rel r by unfold_locales (rule r)
  from Fr well_order_on_domain[OF r] refl_onD[OF r.REFL, of x] have r_def: "r = {(x, x)}" by fast
  interpret wo_rel2 r s by unfold_locales (rule r, rule s)
  have "bij_betw (\<lambda>x. ()) (Field ?L) (Field ?R)"
    unfolding bij_betw_def Field_oexp by (auto simp: r_def FinFunc_singleton)
  moreover have "compat ?L ?R (\<lambda>x. ())" unfolding compat_def oone_def by auto
  ultimately have "iso ?L ?R (\<lambda>x. ())" using s oone_Well_order
    by (subst iso_iff3) (auto intro: oexp_Well_order)
  thus ?thesis using s oone_Well_order unfolding ordIso_def by (auto intro: oexp_Well_order)
qed

(*Lemma 1.4.3 from Holz et al.*)
context
  fixes r s t
  assumes r: "Well_order r"
  assumes s: "Well_order s"
  assumes t: "Well_order t"
begin

lemma osum_ozeroL: "ozero +o r =o r"
  using r unfolding osum_def ozero_def by (auto intro: map_prod_ordIso)

lemma osum_ozeroR: "r +o ozero =o r"
  using r unfolding osum_def ozero_def by (auto intro: map_prod_ordIso)

lemma osum_assoc: "(r +o s) +o t =o r +o s +o t" (is "?L =o ?R")
proof -
  let ?f =
    "\<lambda>rst. case rst of Inl (Inl r) \<Rightarrow> Inl r | Inl (Inr s) \<Rightarrow> Inr (Inl s) | Inr t \<Rightarrow> Inr (Inr t)"
  have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_osum bij_betw_def inj_on_def by (auto simp: image_Un image_iff)
  moreover
  have "compat ?L ?R ?f"
  proof (unfold compat_def, safe)
    fix a b
    assume "(a, b) \<in> ?L"
    thus "(?f a, ?f b) \<in> ?R"
      unfolding osum_def[of "r +o s" t] osum_def[of r "s +o t"] Field_osum
      unfolding osum_def Field_osum image_iff image_Un map_prod_def
      by fastforce
  qed
  ultimately have "iso ?L ?R ?f" using r s t by (subst iso_iff3) (auto intro: osum_Well_order)
  thus ?thesis using r s t unfolding ordIso_def by (auto intro: osum_Well_order)
qed

lemma osum_monoR:
  assumes "s <o t"
  shows "r +o s <o r +o t" (is "?L <o ?R")
proof -
  from assms obtain f where s: "Well_order s" and t:" Well_order t" and "embedS s t f"
    unfolding ordLess_def by blast
  hence *: "inj_on f (Field s)" "compat s t f" "ofilter t (f ` Field s)" "f ` Field s \<subset> Field t"
    using embed_iff_compat_inj_on_ofilter[OF s t, of f] embedS_iff[OF s, of t f]
    unfolding embedS_def by auto
  let ?f = "map_sum id f"
  from *(1) have "inj_on ?f (Field ?L)" unfolding Field_osum inj_on_def by fastforce
  moreover
  from *(2,4) have "compat ?L ?R ?f" unfolding compat_def osum_def map_prod_def by fastforce
  moreover
  interpret t: wo_rel t by unfold_locales (rule t)
  interpret rt: wo_rel ?R by unfold_locales (rule osum_Well_order[OF r t])
  from *(3) have "ofilter ?R (?f ` Field ?L)"
    unfolding t.ofilter_def rt.ofilter_def Field_osum image_Un image_image under_def
    by (auto simp: osum_def intro!: imageI) (auto simp: Field_def)
  ultimately have "embed ?L ?R ?f" using embed_iff_compat_inj_on_ofilter[of ?L ?R ?f]
    by (auto intro: osum_Well_order r s t)
  moreover
  from *(4) have "?f ` Field ?L \<subset> Field ?R" unfolding Field_osum image_Un image_image by auto
  ultimately have "embedS ?L ?R ?f" using embedS_iff[OF osum_Well_order[OF r s], of ?R ?f] by auto
  thus ?thesis unfolding ordLess_def by (auto intro: osum_Well_order r s t)
qed

lemma osum_monoL:
  assumes "r \<le>o s"
  shows "r +o t \<le>o s +o t"
proof -
  from assms obtain f where f: "\<forall>a\<in>Field r. f a \<in> Field s \<and> f ` underS r a \<subseteq> underS s (f a)"
    unfolding ordLeq_def2 by blast
  let ?f = "map_sum f id"
  from f have "\<forall>a\<in>Field (r +o t).
     ?f a \<in> Field (s +o t) \<and> ?f ` underS (r +o t) a \<subseteq> underS (s +o t) (?f a)"
    unfolding Field_osum underS_def by (fastforce simp: osum_def)
  thus ?thesis unfolding ordLeq_def2 by (auto intro: osum_Well_order r s t)
qed

lemma oprod_ozeroL: "ozero *o r =o ozero"
  using ozero_ordIso unfolding ozero_def by simp

lemma oprod_ozeroR: "r *o ozero =o ozero"
  using ozero_ordIso unfolding ozero_def by simp

lemma oprod_ooneR: "r *o oone =o r" (is "?L =o ?R")
proof -
  have "bij_betw fst (Field ?L) (Field ?R)" unfolding Field_oprod bij_betw_def inj_on_def by simp
  moreover have "compat ?L ?R fst" unfolding compat_def oprod_def by auto
  ultimately have "iso ?L ?R fst" using r oone_Well_order
    by (subst iso_iff3) (auto intro: oprod_Well_order)
  thus ?thesis using r oone_Well_order unfolding ordIso_def by (auto intro: oprod_Well_order)
qed

lemma oprod_ooneL: "oone *o r =o r" (is "?L =o ?R")
proof -
  have "bij_betw snd (Field ?L) (Field ?R)" unfolding Field_oprod bij_betw_def inj_on_def by simp
  moreover have "Refl r" by (rule wo_rel.REFL[unfolded wo_rel_def, OF r])
  hence "compat ?L ?R snd" unfolding compat_def oprod_def refl_on_def by auto
  ultimately have "iso ?L ?R snd" using r oone_Well_order
    by (subst iso_iff3) (auto intro: oprod_Well_order)
  thus ?thesis using r oone_Well_order unfolding ordIso_def by (auto intro: oprod_Well_order)
qed

lemma oprod_monoR:
  assumes "ozero <o r" "s <o t"
  shows "r *o s <o r *o t" (is "?L <o ?R")
proof -
  from assms obtain f where s: "Well_order s" and t:" Well_order t" and "embedS s t f"
    unfolding ordLess_def by blast
  hence *: "inj_on f (Field s)" "compat s t f" "ofilter t (f ` Field s)" "f ` Field s \<subset> Field t"
    using embed_iff_compat_inj_on_ofilter[OF s t, of f] embedS_iff[OF s, of t f]
    unfolding embedS_def by auto
  let ?f = "map_prod id f"
  from *(1) have "inj_on ?f (Field ?L)" unfolding Field_oprod inj_on_def by fastforce
  moreover
  from *(2,4) the_inv_into_f_f[OF *(1)] have "compat ?L ?R ?f" unfolding compat_def oprod_def
    by auto (metis well_order_on_domain t, metis well_order_on_domain s)
  moreover
  interpret t: wo_rel t by unfold_locales (rule t)
  interpret rt: wo_rel ?R by unfold_locales (rule oprod_Well_order[OF r t])
  from *(3) have "ofilter ?R (?f ` Field ?L)"
    unfolding t.ofilter_def rt.ofilter_def Field_oprod under_def
    by (auto simp: oprod_def image_iff) (fast | metis r well_order_on_domain)+
  ultimately have "embed ?L ?R ?f" using embed_iff_compat_inj_on_ofilter[of ?L ?R ?f]
    by (auto intro: oprod_Well_order r s t)
  moreover
  from not_ordLess_ordIso[OF assms(1)] have "r \<noteq> {}" by (metis ozero_def ozero_ordIso)
  hence "Field r \<noteq> {}" unfolding Field_def by auto
  with *(4) have "?f ` Field ?L \<subset> Field ?R" unfolding Field_oprod
    by auto (metis SigmaD2 SigmaI map_prod_surj_on)
  ultimately have "embedS ?L ?R ?f" using embedS_iff[OF oprod_Well_order[OF r s], of ?R ?f] by auto
  thus ?thesis unfolding ordLess_def by (auto intro: oprod_Well_order r s t)
qed

lemma oprod_monoL:
  assumes "r \<le>o s"
  shows "r *o t \<le>o s *o t"
proof -
  from assms obtain f where f: "\<forall>a\<in>Field r. f a \<in> Field s \<and> f ` underS r a \<subseteq> underS s (f a)"
    unfolding ordLeq_def2 by blast
  let ?f = "map_prod f id"
  from f have "\<forall>a\<in>Field (r *o t).
     ?f a \<in> Field (s *o t) \<and> ?f ` underS (r *o t) a \<subseteq> underS (s *o t) (?f a)"
    unfolding Field_oprod underS_def unfolding map_prod_def oprod_def by auto
  thus ?thesis unfolding ordLeq_def2 by (auto intro: oprod_Well_order r s t)
qed

lemma oprod_assoc: "(r *o s) *o t =o r *o s *o t" (is "?L =o ?R")
proof -
  let ?f = "\<lambda>((a,b),c). (a,b,c)"
  have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding Field_oprod bij_betw_def inj_on_def by (auto simp: image_Un image_iff)
  moreover
  have "compat ?L ?R ?f"
  proof (unfold compat_def, safe)
    fix a1 a2 a3 b1 b2 b3
    assume "(((a1, a2), a3), ((b1, b2), b3)) \<in> ?L"
    thus "((a1, a2, a3), (b1, b2, b3)) \<in> ?R"
      unfolding oprod_def[of "r *o s" t] oprod_def[of r "s *o t"] Field_oprod
      unfolding oprod_def Field_oprod image_iff image_Un by fast
  qed
  ultimately have "iso ?L ?R ?f" using r s t by (subst iso_iff3) (auto intro: oprod_Well_order)
  thus ?thesis using r s t unfolding ordIso_def by (auto intro: oprod_Well_order)
qed

lemma oprod_osum: "r *o (s +o t) =o r *o s +o r *o t" (is "?L =o ?R")
proof -
  let ?f = "\<lambda>(a,bc). case bc of Inl b \<Rightarrow> Inl (a, b) | Inr c \<Rightarrow> Inr (a, c)"
  have "bij_betw ?f (Field ?L) (Field ?R)" unfolding Field_oprod Field_osum bij_betw_def inj_on_def
    by (fastforce simp: image_Un image_iff split: sum.splits)
  moreover
  have "compat ?L ?R ?f"
  proof (unfold compat_def, intro allI impI)
    fix a b
    assume "(a, b) \<in> ?L"
    thus "(?f a, ?f b) \<in> ?R"
      unfolding oprod_def[of r "s +o t"] osum_def[of "r *o s" "r *o t"] Field_oprod Field_osum
      unfolding oprod_def osum_def Field_oprod Field_osum image_iff image_Un by auto
  qed
  ultimately have "iso ?L ?R ?f" using r s t
    by (subst iso_iff3) (auto intro: oprod_Well_order osum_Well_order)
  thus ?thesis using r s t unfolding ordIso_def by (auto intro: oprod_Well_order osum_Well_order)
qed

lemma ozero_oexp: "\<not> (s =o ozero) \<Longrightarrow> ozero ^o s =o ozero"
  by (fastforce simp add: oexp_def[OF ozero_Well_order s] FinFunc_def Func_def intro: FieldI1)

lemma oone_oexp: "oone ^o s =o oone" (is "?L =o ?R")
  by (rule oone_ordIso_oexp[OF ordIso_reflexive[OF oone_Well_order] s])

lemma oexp_monoR:
  assumes "oone <o r" "s <o t"
  shows   "r ^o s <o r ^o t" (is "?L <o ?R")
proof -
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rt: wo_rel2 r t by unfold_locales (rule r, rule t)
  interpret rexpt: wo_rel "r ^o t" by unfold_locales (rule rt.oexp_Well_order)
  interpret r: wo_rel r by unfold_locales (rule r)
  interpret s: wo_rel s by unfold_locales (rule s)
  interpret t: wo_rel t by unfold_locales (rule t)
  have "Field r \<noteq> {}" by (metis assms(1) internalize_ordLess not_psubset_empty)
  moreover
  { assume "Field r = {r.zero}"
    hence "r = {(r.zero, r.zero)}" using refl_onD[OF r.REFL, of r.zero] unfolding Field_def by auto
    hence "r =o oone" by (metis oone_ordIso ordIso_symmetric)
    with not_ordLess_ordIso[OF assms(1)] have False by (metis ordIso_symmetric)
  }
  ultimately obtain x where x: "x \<in> Field r" "r.zero \<in> Field r" "x \<noteq> r.zero"
    by (metis insert_iff r.zero_in_Field subsetI subset_singletonD)
  moreover from assms(2) obtain f where "embedS s t f" unfolding ordLess_def by blast
  hence *: "inj_on f (Field s)" "compat s t f" "ofilter t (f ` Field s)" "f ` Field s \<subset> Field t"
    using embed_iff_compat_inj_on_ofilter[OF s t, of f] embedS_iff[OF s, of t f]
    unfolding embedS_def by auto
  note invff = the_inv_into_f_f[OF *(1)] and injfD = inj_onD[OF *(1)]
  define F where [abs_def]: "F g z =
    (if z \<in> f ` Field s then g (the_inv_into (Field s) f z)
     else if z \<in> Field t then r.zero else undefined)" for g z
  from *(4) x(2) the_inv_into_f_eq[OF *(1)] have FLR: "F ` Field ?L \<subseteq> Field ?R"
    unfolding rt.Field_oexp rs.Field_oexp FinFunc_def Func_def fin_support_def support_def F_def
    by (fastforce split: option.splits if_split_asm elim!: finite_surj[of _ _ f])
  have "inj_on F (Field ?L)" unfolding rs.Field_oexp inj_on_def fun_eq_iff
  proof safe
    fix g h x assume "g \<in> FinFunc r s" "h \<in> FinFunc r s" "\<forall>y. F g y = F h y"
    with invff show "g x = h x" unfolding F_def fun_eq_iff FinFunc_def Func_def
      by auto (metis image_eqI)
  qed
  moreover
  have "compat ?L ?R F" unfolding compat_def rs.oexp_def rt.oexp_def
  proof (safe elim!: bspec[OF iffD1[OF image_subset_iff FLR[unfolded rs.Field_oexp rt.Field_oexp]]])
    fix g h assume gh: "g \<in> FinFunc r s" "h \<in> FinFunc r s" "F g \<noteq> F h"
      "let m = s.max_fun_diff g h in (g m, h m) \<in> r"
    hence "g \<noteq> h" by auto
    note max_fun_diff_in = rs.max_fun_diff_in[OF \<open>g \<noteq> h\<close> gh(1,2)]
      and max_fun_diff_max = rs.max_fun_diff_max[OF \<open>g \<noteq> h\<close> gh(1,2)]
    with *(4) invff *(2) have "t.max_fun_diff (F g) (F h) = f (s.max_fun_diff g h)"
      unfolding t.max_fun_diff_def compat_def
      by (intro t.maxim_equality) (auto simp: t.isMaxim_def F_def dest: injfD)
    with gh invff max_fun_diff_in
    show "let m = t.max_fun_diff (F g) (F h) in (F g m, F h m) \<in> r"
      unfolding F_def Let_def by (auto simp: dest: injfD)
  qed
  moreover
  from FLR have "ofilter ?R (F ` Field ?L)"
    unfolding rexpt.ofilter_def under_def rs.Field_oexp rt.Field_oexp unfolding rt.oexp_def
  proof (safe elim!: imageI)
    fix g h assume gh: "g \<in> FinFunc r s" "h \<in> FinFunc r t" "F g \<in> FinFunc r t"
      "let m = t.max_fun_diff h (F g) in (h m, F g m) \<in> r"
    thus "h \<in> F ` FinFunc r s"
    proof (cases "h = F g")
      case False
      hence max_Field: "t.max_fun_diff h (F g) \<in> {a \<in> Field t. h a \<noteq> F g a}"
        by (rule rt.max_fun_diff_in[OF _ gh(2,3)])
      { assume *: "t.max_fun_diff h (F g) \<notin> f ` Field s"
        with max_Field have **: "F g (t.max_fun_diff h (F g)) = r.zero" unfolding F_def by auto
        with * gh(4) have "h (t.max_fun_diff h (F g)) = r.zero" unfolding Let_def by auto
        with ** have False using max_Field gh(2,3) unfolding FinFunc_def Func_def by auto
      }
      hence max_f_Field: "t.max_fun_diff h (F g) \<in> f ` Field s" by blast
      { fix z assume z: "z \<in> Field t - f ` Field s"
        have "(t.max_fun_diff h (F g), z) \<in> t"
        proof (rule ccontr)
          assume "(t.max_fun_diff h (F g), z) \<notin> t"
          hence "(z, t.max_fun_diff h (F g)) \<in> t" using t.in_notinI[of "t.max_fun_diff h (F g)" z]
              z max_Field by auto
          hence "z \<in> f ` Field s" using *(3) max_f_Field unfolding t.ofilter_def under_def
            by fastforce
          with z show False by blast
        qed
        hence "h z = r.zero" using rt.max_fun_diff_le_eq[OF _ False gh(2,3), of z]
            z max_f_Field unfolding F_def by auto
      } note ** = this
      with *(3) gh(2) have "h = F (\<lambda>x. if x \<in> Field s then h (f x) else undefined)" using invff
        unfolding F_def fun_eq_iff FinFunc_def Func_def Let_def t.ofilter_def under_def by auto
      moreover from gh(2) *(1,3) have "(\<lambda>x. if x \<in> Field s then h (f x) else undefined) \<in> FinFunc r s"
        unfolding FinFunc_def Func_def fin_support_def support_def t.ofilter_def under_def
        by (auto intro: subset_inj_on elim!: finite_imageD[OF finite_subset[rotated]])
      ultimately show "?thesis" by (rule image_eqI)
    qed simp
  qed
  ultimately have "embed ?L ?R F" using embed_iff_compat_inj_on_ofilter[of ?L ?R F]
    by (auto intro: oexp_Well_order r s t)
  moreover
  from FLR have "F ` Field ?L \<subset> Field ?R"
  proof (intro psubsetI)
    from *(4) obtain z where z: "z \<in> Field t" "z \<notin> f ` Field s" by auto
    define h where [abs_def]: "h z' =
      (if z' \<in> Field t then if z' = z then x else r.zero else undefined)" for z'
    from z x(3) have "rt.SUPP h = {z}" unfolding support_def h_def by simp
    with x have "h \<in> Field ?R" unfolding h_def rt.Field_oexp FinFunc_def Func_def fin_support_def
      by auto
    moreover
    { fix g
      from z have "F g z = r.zero" "h z = x" unfolding support_def h_def F_def by auto
      with x(3) have "F g \<noteq> h" unfolding fun_eq_iff by fastforce
    }
    hence "h \<notin> F ` Field ?L" by blast
    ultimately show "F ` Field ?L \<noteq> Field ?R" by blast
  qed
  ultimately have "embedS ?L ?R F" using embedS_iff[OF rs.oexp_Well_order, of ?R F] by auto
  thus ?thesis unfolding ordLess_def using r s t by (auto intro: oexp_Well_order)
qed

lemma oexp_monoL:
  assumes "r \<le>o s"
  shows   "r ^o t \<le>o s ^o t"
proof -
  interpret rt: wo_rel2 r t by unfold_locales (rule r, rule t)
  interpret st: wo_rel2 s t by unfold_locales (rule s, rule t)
  interpret r: wo_rel r by unfold_locales (rule r)
  interpret s: wo_rel s by unfold_locales (rule s)
  interpret t: wo_rel t by unfold_locales (rule t)
  show ?thesis
  proof (cases "t = {}")
    case True thus ?thesis using r s unfolding ordLeq_def2 underS_def by auto
  next
    case False thus ?thesis
    proof (cases "r = {}")
      case True thus ?thesis using t \<open>t \<noteq> {}\<close> st.oexp_Well_order ozero_ordLeq[unfolded ozero_def]
        by auto
    next
      case False
      from assms obtain f where f: "embed r s f" unfolding ordLeq_def by blast
      hence f_underS: "\<forall>a\<in>Field r. f a \<in> Field s \<and> f ` underS r a \<subseteq> underS s (f a)"
        using embed_in_Field embed_underS2 rt.rWELL by fastforce
      from f \<open>t \<noteq> {}\<close> False have *: "Field r \<noteq> {}" "Field s \<noteq> {}" "Field t \<noteq> {}"
        unfolding Field_def embed_def under_def bij_betw_def by auto
      with f obtain x where "s.zero = f x" "x \<in> Field r" unfolding embed_def bij_betw_def
        using s.zero_under subsetD[OF under_Field[of r]]
        by (metis (no_types, lifting) f_inv_into_f f_underS inv_into_into r.zero_in_Field)
      with f have fz: "f r.zero = s.zero" and inj: "inj_on f (Field r)" and compat: "compat r s f"
        unfolding embed_iff_compat_inj_on_ofilter[OF r s] compat_def
        by (fastforce intro: s.leq_zero_imp)+
      let ?f = "\<lambda>g x. if x \<in> Field t then f (g x) else undefined"
      { fix g assume g: "g \<in> Field (r ^o t)"
        with fz f_underS have Field_fg: "?f g \<in> Field (s ^o t)"
          unfolding st.Field_oexp rt.Field_oexp FinFunc_def Func_def fin_support_def support_def
          by (auto elim!: finite_subset[rotated])
        moreover
        have "?f ` underS (r ^o t) g \<subseteq> underS (s ^o t) (?f g)"
        proof safe
          fix h
          assume h_underS: "h \<in> underS (r ^o t) g"
          hence "h \<in> Field (r ^o t)" unfolding underS_def Field_def by auto
          with fz f_underS have Field_fh: "?f h \<in> Field (s ^o t)"
            unfolding st.Field_oexp rt.Field_oexp FinFunc_def Func_def fin_support_def support_def
            by (auto elim!: finite_subset[rotated])
          from h_underS have "h \<noteq> g" and hg: "(h, g) \<in> rt.oexp" unfolding underS_def by auto
          with f inj have neq: "?f h \<noteq> ?f g"
            unfolding fun_eq_iff inj_on_def rt.oexp_def map_option_case FinFunc_def Func_def Let_def
            by simp metis
          with hg have "t.max_fun_diff (?f h) (?f g) = t.max_fun_diff h g" unfolding rt.oexp_def
            using rt.max_fun_diff[OF \<open>h \<noteq> g\<close>] rt.max_fun_diff_in[OF \<open>h \<noteq> g\<close>]
            by (subst t.max_fun_diff_def, intro t.maxim_equality)
              (auto simp: t.isMaxim_def intro: inj_onD[OF inj] intro!: rt.max_fun_diff_max)
          with Field_fg Field_fh hg fz f_underS compat neq have "(?f h, ?f g) \<in> st.oexp"
            using rt.max_fun_diff[OF \<open>h \<noteq> g\<close>] rt.max_fun_diff_in[OF \<open>h \<noteq> g\<close>] unfolding st.Field_oexp
            unfolding rt.oexp_def st.oexp_def Let_def compat_def by auto
          with neq show "?f h \<in> underS (s ^o t) (?f g)" unfolding underS_def by auto
        qed
        ultimately have "?f g \<in> Field (s ^o t) \<and> ?f ` underS (r ^o t) g \<subseteq> underS (s ^o t) (?f g)"
          by blast
      }
      thus ?thesis unfolding ordLeq_def2 by (fastforce intro: oexp_Well_order r s t)
    qed
  qed
qed

lemma ordLeq_oexp2:
  assumes "oone <o r"
  shows   "s \<le>o r ^o s"
proof -
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret r: wo_rel r by unfold_locales (rule r)
  interpret s: wo_rel s by unfold_locales (rule s)
  from assms well_order_on_domain[OF r] obtain x where
    x: "x \<in> Field r" "r.zero \<in> Field r" "x \<noteq> r.zero"
    unfolding ordLess_def oone_def embedS_def[abs_def] bij_betw_def embed_def under_def
    by (auto simp: image_def)
      (metis (lifting) equals0D mem_Collect_eq r.zero_in_Field singletonI)
  let ?f = "\<lambda>a b. if b \<in> Field s then if b = a then x else r.zero else undefined"
  from x(3) have SUPP: "\<And>y. y \<in> Field s \<Longrightarrow> rs.SUPP (?f y) = {y}" unfolding support_def by auto
  { fix y assume y: "y \<in> Field s"
    with x(1,2) SUPP have "?f y \<in> Field (r ^o s)" unfolding rs.Field_oexp
      by (auto simp: FinFunc_def Func_def fin_support_def)
    moreover
    have "?f ` underS s y \<subseteq> underS (r ^o s) (?f y)"
    proof safe
      fix z
      assume "z \<in> underS s y"
      hence z: "z \<noteq> y" "(z, y) \<in> s" "z \<in> Field s" unfolding underS_def Field_def by auto
      from x(3) y z(1,3) have "?f z \<noteq> ?f y" unfolding fun_eq_iff by auto
      moreover
      { from x(1,2) have "?f z \<in> FinFunc r s" "?f y \<in> FinFunc r s"
          unfolding FinFunc_def Func_def fin_support_def by (auto simp: SUPP[OF z(3)] SUPP[OF y])
        moreover
        from x(3) y z(1,2) refl_onD[OF s.REFL] have "s.max_fun_diff (?f z) (?f y) = y"
          unfolding rs.max_fun_diff_alt SUPP[OF z(3)] SUPP[OF y]
          by (intro s.maxim_equality) (auto simp: s.isMaxim_def)
        ultimately have "(?f z, ?f y) \<in> rs.oexp" using y x(1)
          unfolding rs.oexp_def Let_def by auto
      }
      ultimately show "?f z \<in> underS (r ^o s) (?f y)" unfolding underS_def by blast
    qed
    ultimately have "?f y \<in> Field (r ^o s) \<and> ?f ` underS s y \<subseteq> underS (r ^o s) (?f y)" by blast
  }
  thus ?thesis unfolding ordLeq_def2 by (fast intro: oexp_Well_order r s)
qed

lemma FinFunc_osum:
  "fg \<in> FinFunc r (s +o t) = (fg o Inl \<in> FinFunc r s \<and> fg o Inr \<in> FinFunc r t)"
  (is "?L = (?R1 \<and> ?R2)")
proof safe
  assume ?L
  from \<open>?L\<close> show ?R1 unfolding FinFunc_def Field_osum Func_def Int_iff fin_support_Field_osum o_def
    by (auto split: sum.splits)
  from \<open>?L\<close> show ?R2 unfolding FinFunc_def Field_osum Func_def Int_iff fin_support_Field_osum o_def
    by (auto split: sum.splits)
next
  assume ?R1 ?R2
  thus "?L" unfolding FinFunc_def Field_osum Func_def
    by (auto simp: fin_support_Field_osum o_def image_iff split: sum.splits) (metis sumE)
qed

lemma max_fun_diff_eq_Inl:
  assumes "wo_rel.max_fun_diff (s +o t) (case_sum f1 g1) (case_sum f2 g2) = Inl x"
    "case_sum f1 g1 \<noteq> case_sum f2 g2"
    "case_sum f1 g1 \<in> FinFunc r (s +o t)" "case_sum f2 g2 \<in> FinFunc r (s +o t)"
  shows "wo_rel.max_fun_diff s f1 f2 = x" (is ?P) "g1 = g2" (is ?Q)
proof -
  interpret st: wo_rel "s +o t" by unfold_locales (rule osum_Well_order[OF s t])
  interpret s: wo_rel s by unfold_locales (rule s)
  interpret rst: wo_rel2 r "s +o t" by unfold_locales (rule r, rule osum_Well_order[OF s t])
  from assms(1) have *: "st.isMaxim {a \<in> Field (s +o t). case_sum f1 g1 a \<noteq> case_sum f2 g2 a} (Inl x)"
    using rst.isMaxim_max_fun_diff[OF assms(2-4)] by simp
  hence "s.isMaxim {a \<in> Field s. f1 a \<noteq> f2 a} x"
    unfolding st.isMaxim_def s.isMaxim_def Field_osum by (auto simp: osum_def)
  thus ?P unfolding s.max_fun_diff_def by (rule s.maxim_equality)
  from assms(3,4) have **: "g1 \<in> FinFunc r t" "g2 \<in> FinFunc r t" unfolding FinFunc_osum
    by (auto simp: o_def)
  show ?Q
  proof
    fix x
    from * ** show "g1 x = g2 x" unfolding st.isMaxim_def Field_osum FinFunc_def Func_def fun_eq_iff
      unfolding osum_def by (case_tac "x \<in> Field t") auto
  qed
qed

lemma max_fun_diff_eq_Inr:
  assumes "wo_rel.max_fun_diff (s +o t) (case_sum f1 g1) (case_sum f2 g2) = Inr x"
    "case_sum f1 g1 \<noteq> case_sum f2 g2"
    "case_sum f1 g1 \<in> FinFunc r (s +o t)" "case_sum f2 g2 \<in> FinFunc r (s +o t)"
  shows "wo_rel.max_fun_diff t g1 g2 = x" (is ?P) "g1 \<noteq> g2" (is ?Q)
proof -
  interpret st: wo_rel "s +o t" by unfold_locales (rule osum_Well_order[OF s t])
  interpret t: wo_rel t by unfold_locales (rule t)
  interpret rst: wo_rel2 r "s +o t" by unfold_locales (rule r, rule osum_Well_order[OF s t])
  from assms(1) have *: "st.isMaxim {a \<in> Field (s +o t). case_sum f1 g1 a \<noteq> case_sum f2 g2 a} (Inr x)"
    using rst.isMaxim_max_fun_diff[OF assms(2-4)] by simp
  hence "t.isMaxim {a \<in> Field t. g1 a \<noteq> g2 a} x"
    unfolding st.isMaxim_def t.isMaxim_def Field_osum by (auto simp: osum_def)
  thus ?P ?Q unfolding t.max_fun_diff_def fun_eq_iff
    by (auto intro: t.maxim_equality simp: t.isMaxim_def)
qed

lemma oexp_osum: "r ^o (s +o t) =o (r ^o s) *o (r ^o t)" (is "?R =o ?L")
proof (rule ordIso_symmetric)
  interpret rst: wo_rel2 r "s +o t" by unfold_locales (rule r, rule osum_Well_order[OF s t])
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rt: wo_rel2 r t by unfold_locales (rule r, rule t)
  let ?f = "\<lambda>(f, g). case_sum f g"
  have "bij_betw ?f (Field ?L) (Field ?R)"
    unfolding bij_betw_def rst.Field_oexp rs.Field_oexp rt.Field_oexp Field_oprod proof (intro conjI)
    show "inj_on ?f (FinFunc r s \<times> FinFunc r t)" unfolding inj_on_def
      by (auto simp: fun_eq_iff split: sum.splits)
    show "?f ` (FinFunc r s \<times> FinFunc r t) = FinFunc r (s +o t)"
    proof safe
      fix fg assume "fg \<in> FinFunc r (s +o t)"
      thus "fg \<in> ?f ` (FinFunc r s \<times> FinFunc r t)"
        by (intro image_eqI[of _ _ "(fg o Inl, fg o Inr)"])
          (auto simp: FinFunc_osum fun_eq_iff split: sum.splits)
    qed (auto simp: FinFunc_osum o_def)
  qed
  moreover have "compat ?L ?R ?f"
    unfolding compat_def rst.Field_oexp rs.Field_oexp rt.Field_oexp oprod_def
    unfolding rst.oexp_def Let_def rs.oexp_def rt.oexp_def
    by (fastforce simp: Field_osum FinFunc_osum o_def split: sum.splits
        dest: max_fun_diff_eq_Inl max_fun_diff_eq_Inr)
  ultimately have "iso ?L ?R ?f" using r s t
    by (subst iso_iff3) (auto intro: oexp_Well_order oprod_Well_order osum_Well_order)
  thus "?L =o ?R" using r s t unfolding ordIso_def
    by (auto intro: oexp_Well_order oprod_Well_order osum_Well_order)
qed

definition "rev_curr f b = (if b \<in> Field t then \<lambda>a. f (a, b) else undefined)"

lemma rev_curr_FinFunc:
  assumes Field: "Field r \<noteq> {}"
  shows "rev_curr ` (FinFunc r (s *o t)) = FinFunc (r ^o s) t"
proof safe
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rst: wo_rel2 "r ^o s" t by unfold_locales (rule oexp_Well_order[OF r s], rule t)
  fix g assume g: "g \<in> FinFunc r (s *o t)"
  hence "finite (rst.SUPP (rev_curr g))" "\<forall>x \<in> Field t. finite (rs.SUPP (rev_curr g x))"
    unfolding FinFunc_def Field_oprod rs.Field_oexp Func_def fin_support_def support_def
      rs.zero_oexp[OF Field] rev_curr_def by (auto simp: fun_eq_iff rs.const_def elim!: finite_surj)
  with g show "rev_curr g \<in> FinFunc (r ^o s) t"
    unfolding FinFunc_def Field_oprod rs.Field_oexp Func_def
    by (auto simp: rev_curr_def fin_support_def)
next
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rst: wo_rel2 "r ^o s" t by unfold_locales (rule oexp_Well_order[OF r s], rule t)
  fix fg assume *: "fg \<in> FinFunc (r ^o s) t"
  let ?g = "\<lambda>(a, b). if (a, b) \<in> Field (s *o t) then fg b a else undefined"
  show "fg \<in> rev_curr ` FinFunc r (s *o t)"
  proof (rule image_eqI[of _ _ ?g])
    show "fg = rev_curr ?g"
    proof
      fix x
      from * show "fg x = rev_curr ?g x"
        unfolding FinFunc_def rs.Field_oexp Func_def rev_curr_def Field_oprod by auto
    qed
  next
    have **: "(\<Union>g \<in> fg ` Field t. rs.SUPP g) =
              (\<Union>g \<in> fg ` Field t - {rs.const}. rs.SUPP g)"
      unfolding support_def by auto
    from * have ***: "\<forall>g \<in> fg ` Field t. finite (rs.SUPP g)" "finite (rst.SUPP fg)"
      unfolding rs.Field_oexp FinFunc_def Func_def fin_support_def Option.these_def by force+
    hence "finite (fg ` Field t - {rs.const})" using *
      unfolding support_def rs.zero_oexp[OF Field] FinFunc_def Func_def
      by (elim finite_surj[of _ _ fg]) (fastforce simp: image_iff Option.these_def)
    with *** have "finite ((\<Union>g \<in> fg ` Field t. rs.SUPP g) \<times> rst.SUPP fg)"
      by (subst **) (auto intro!: finite_cartesian_product)
    with * show "?g \<in> FinFunc r (s *o t)"
      unfolding Field_oprod rs.Field_oexp FinFunc_def Func_def fin_support_def Option.these_def
        support_def rs.zero_oexp[OF Field] by (auto elim!: finite_subset[rotated])
  qed
qed

lemma rev_curr_app_FinFunc[elim!]:
  "\<lbrakk>f \<in> FinFunc r (s *o t); z \<in> Field t\<rbrakk> \<Longrightarrow> rev_curr f z \<in> FinFunc r s"
  unfolding rev_curr_def FinFunc_def Func_def Field_oprod fin_support_def support_def
  by (auto elim: finite_surj)

lemma max_fun_diff_oprod:
  assumes Field: "Field r \<noteq> {}" and "f \<noteq> g" "f \<in> FinFunc r (s *o t)" "g \<in> FinFunc r (s *o t)"
  defines "m \<equiv> wo_rel.max_fun_diff t (rev_curr f) (rev_curr g)"
  shows "wo_rel.max_fun_diff (s *o t) f g =
    (wo_rel.max_fun_diff s (rev_curr f m) (rev_curr g m), m)"
proof -
  interpret st: wo_rel "s *o t" by unfold_locales (rule oprod_Well_order[OF s t])
  interpret s: wo_rel s by unfold_locales (rule s)
  interpret t: wo_rel t by unfold_locales (rule t)
  interpret r_st: wo_rel2 r "s *o t" by unfold_locales (rule r, rule oprod_Well_order[OF s t])
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rst: wo_rel2 "r ^o s" t by unfold_locales (rule oexp_Well_order[OF r s], rule t)
  from fun_unequal_in_support[OF assms(2), of "Field (s *o t)" "Field r" "Field r"] assms(3,4)
  have diff1: "rev_curr f \<noteq> rev_curr g"
    "rev_curr f \<in> FinFunc (r ^o s) t" "rev_curr g \<in> FinFunc (r ^o s) t" using rev_curr_FinFunc[OF Field]
    unfolding fun_eq_iff rev_curr_def[abs_def] FinFunc_def support_def Field_oprod
    by auto fast
  hence diff2: "rev_curr f m \<noteq> rev_curr g m" "rev_curr f m \<in> FinFunc r s" "rev_curr g m \<in> FinFunc r s"
    using rst.max_fun_diff[OF diff1] assms(3,4) rst.max_fun_diff_in unfolding m_def by auto
  show ?thesis unfolding st.max_fun_diff_def
  proof (intro st.maxim_equality, unfold st.isMaxim_def Field_oprod, safe)
    show "s.max_fun_diff (rev_curr f m) (rev_curr g m) \<in> Field s"
      using rs.max_fun_diff_in[OF diff2] by auto
  next
    show "m \<in> Field t" using rst.max_fun_diff_in[OF diff1] unfolding m_def by auto
  next
    assume "f (s.max_fun_diff (rev_curr f m) (rev_curr g m), m) =
            g (s.max_fun_diff (rev_curr f m) (rev_curr g m), m)"
      (is "f (?x, m) = g (?x, m)")
    hence "rev_curr f m ?x = rev_curr g m ?x" unfolding rev_curr_def by auto
    with rs.max_fun_diff[OF diff2] show False by auto
  next
    fix x y assume "f (x, y) \<noteq> g (x, y)" "x \<in> Field s" "y \<in> Field t"
    thus "((x, y), (s.max_fun_diff (rev_curr f m) (rev_curr g m), m)) \<in> s *o t"
      using rst.max_fun_diff_in[OF diff1] rs.max_fun_diff_in[OF diff2] diff1 diff2
        rst.max_fun_diff_max[OF diff1, of y] rs.max_fun_diff_le_eq[OF _ diff2, of x]
      unfolding oprod_def m_def rev_curr_def fun_eq_iff by (auto intro: s.in_notinI)
  qed
qed

lemma oexp_oexp: "(r ^o s) ^o t =o r ^o (s *o t)" (is "?R =o ?L")
proof (cases "r = {}")
  case True
  interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
  interpret rst: wo_rel2 "r ^o s" t by unfold_locales (rule oexp_Well_order[OF r s], rule t)
  show ?thesis
  proof (cases "s = {} \<or> t = {}")
    case True with \<open>r = {}\<close> show ?thesis
      by (auto simp: oexp_empty[OF oexp_Well_order[OF Well_order_empty s]]
          intro!: ordIso_transitive[OF ordIso_symmetric[OF oone_ordIso] oone_ordIso]
          ordIso_transitive[OF oone_ordIso_oexp[OF ordIso_symmetric[OF oone_ordIso] t] oone_ordIso])
  next
    case False
    hence "s *o t \<noteq> {}" unfolding oprod_def Field_def by fastforce
    with False show ?thesis
      using \<open>r = {}\<close> ozero_ordIso
      by (auto simp add: s t oprod_Well_order ozero_def)
  qed
next
  case False
  hence Field: "Field r \<noteq> {}" by (metis Field_def Range_empty_iff Un_empty)
  show ?thesis
  proof (rule ordIso_symmetric)
    interpret r_st: wo_rel2 r "s *o t" by unfold_locales (rule r, rule oprod_Well_order[OF s t])
    interpret rs: wo_rel2 r s by unfold_locales (rule r, rule s)
    interpret rst: wo_rel2 "r ^o s" t by unfold_locales (rule oexp_Well_order[OF r s], rule t)
    have bij: "bij_betw rev_curr (Field ?L) (Field ?R)"
      unfolding bij_betw_def r_st.Field_oexp rst.Field_oexp Field_oprod proof (intro conjI)
      show "inj_on rev_curr (FinFunc r (s *o t))"
        unfolding inj_on_def FinFunc_def Func_def Field_oprod rs.Field_oexp rev_curr_def[abs_def]
        by (auto simp: fun_eq_iff) metis
      show "rev_curr ` (FinFunc r (s *o t)) = FinFunc (r ^o s) t" by (rule rev_curr_FinFunc[OF Field])
    qed
    moreover
    have "compat ?L ?R rev_curr"
      unfolding compat_def proof safe
      fix fg1 fg2 assume fg: "(fg1, fg2) \<in> r ^o (s *o t)"
      show "(rev_curr fg1, rev_curr fg2) \<in> r ^o s ^o t"
      proof (cases "fg1 = fg2")
        assume "fg1 \<noteq> fg2"
        with fg show ?thesis
          using rst.max_fun_diff_in[of "rev_curr fg1" "rev_curr fg2"]
            max_fun_diff_oprod[OF Field, of fg1 fg2]  rev_curr_FinFunc[OF Field, symmetric]
          unfolding r_st.Field_oexp rs.Field_oexp rst.Field_oexp unfolding r_st.oexp_def rst.oexp_def
          by (auto simp: rs.oexp_def Let_def) (auto simp: rev_curr_def[abs_def])
      next
        assume "fg1 = fg2"
        with fg bij show ?thesis unfolding r_st.Field_oexp rs.Field_oexp rst.Field_oexp bij_betw_def
          by (auto simp: r_st.oexp_def rst.oexp_def)
      qed
    qed
    ultimately have "iso ?L ?R rev_curr" using r s t
      by (subst iso_iff3) (auto intro: oexp_Well_order oprod_Well_order)
    thus "?L =o ?R" using r s t unfolding ordIso_def
      by (auto intro: oexp_Well_order oprod_Well_order)
  qed
qed

end (* context with 3 wellorders *)

end
