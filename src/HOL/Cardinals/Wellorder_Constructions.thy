(*  Title:      HOL/Cardinals/Wellorder_Constructions.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Constructions on wellorders.
*)

section \<open>Constructions on Wellorders\<close>

theory Wellorder_Constructions
  imports
    Wellorder_Embedding Order_Union
begin

unbundle cardinal_syntax

declare
  ordLeq_Well_order_simp[simp]
  not_ordLeq_iff_ordLess[simp]
  not_ordLess_iff_ordLeq[simp]
  Func_empty[simp]
  Func_is_emp[simp]



subsection \<open>Order filters versus restrictions and embeddings\<close>

lemma ofilter_subset_iso:
  assumes WELL: "Well_order r" and
    OFA: "ofilter r A" and OFB: "ofilter r B"
  shows "(A = B) = iso (Restr r A) (Restr r B) id"
  using assms by (auto simp add: ofilter_subset_embedS_iso)


subsection \<open>Ordering the well-orders by existence of embeddings\<close>

corollary ordLeq_refl_on: "refl_on {r. Well_order r} ordLeq"
  using ordLeq_reflexive unfolding ordLeq_def refl_on_def
  by blast

corollary ordLeq_trans: "trans ordLeq"
  using trans_def[of ordLeq] ordLeq_transitive by blast

corollary ordLeq_preorder_on: "preorder_on {r. Well_order r} ordLeq"
  by(auto simp add: preorder_on_def ordLeq_refl_on ordLeq_trans)

corollary ordIso_subset: "ordIso \<subseteq> {r. Well_order r} \<times> {r. Well_order r}"
  using ordIso_reflexive unfolding refl_on_def ordIso_def by blast

corollary ordIso_refl_on: "refl_on {r. Well_order r} ordIso"
  using ordIso_reflexive unfolding refl_on_def ordIso_def
  by blast

corollary ordIso_trans: "trans ordIso"
  using trans_def[of ordIso] ordIso_transitive by blast

corollary ordIso_sym: "sym ordIso"
  by (auto simp add: sym_def ordIso_symmetric)

corollary ordIso_equiv: "equiv {r. Well_order r} ordIso"
  using ordIso_subset ordIso_refl_on ordIso_sym ordIso_trans by (intro equivI)

lemma ordLess_Well_order_simp[simp]:
  assumes "r <o r'"
  shows "Well_order r \<and> Well_order r'"
  using assms unfolding ordLess_def by simp

lemma ordIso_Well_order_simp[simp]:
  assumes "r =o r'"
  shows "Well_order r \<and> Well_order r'"
  using assms unfolding ordIso_def by simp

lemma ordLess_irrefl: "irrefl ordLess"
  by(unfold irrefl_def, auto simp add: ordLess_irreflexive)

lemma ordLess_or_ordIso:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "r <o r' \<or> r' <o r \<or> r =o r'"
  unfolding ordLess_def ordIso_def
  using assms embedS_or_iso[of r r'] by auto

corollary ordLeq_ordLess_Un_ordIso:
  "ordLeq = ordLess \<union> ordIso"
  by (auto simp add: ordLeq_iff_ordLess_or_ordIso)

lemma ordIso_or_ordLess:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "r =o r' \<or> r <o r' \<or> r' <o r"
  using assms ordLess_or_ordLeq ordLeq_iff_ordLess_or_ordIso by blast

lemmas ord_trans = ordIso_transitive ordLeq_transitive ordLess_transitive
  ordIso_ordLeq_trans ordLeq_ordIso_trans
  ordIso_ordLess_trans ordLess_ordIso_trans
  ordLess_ordLeq_trans ordLeq_ordLess_trans

lemma ofilter_ordLeq:
  assumes "Well_order r" and "ofilter r A"
  shows "Restr r A \<le>o r"
by (metis assms inf.orderE ofilter_embed ofilter_subset_ordLeq refl_on_def wo_rel.Field_ofilter wo_rel.REFL wo_rel.intro)

corollary under_Restr_ordLeq:
  "Well_order r \<Longrightarrow> Restr r (under r a) \<le>o r"
  by (auto simp add: ofilter_ordLeq wo_rel.under_ofilter wo_rel_def)


subsection \<open>Copy via direct images\<close>

lemma Id_dir_image: "dir_image Id f \<le> Id"
  unfolding dir_image_def by auto

lemma Un_dir_image:
  "dir_image (r1 \<union> r2) f = (dir_image r1 f) \<union> (dir_image r2 f)"
  unfolding dir_image_def by auto

lemma Int_dir_image:
  assumes "inj_on f (Field r1 \<union> Field r2)"
  shows "dir_image (r1 Int r2) f = (dir_image r1 f) Int (dir_image r2 f)"
proof
  show "dir_image (r1 Int r2) f \<le> (dir_image r1 f) Int (dir_image r2 f)"
    using assms unfolding dir_image_def inj_on_def by auto
next
  show "(dir_image r1 f) Int (dir_image r2 f) \<le> dir_image (r1 Int r2) f"
    by (clarsimp simp: dir_image_def) (metis FieldI1 FieldI2 UnCI assms inj_on_def)
qed

(* More facts on ordinal sum: *)

lemma Osum_embed:
  assumes FLD: "Field r Int Field r' = {}" and
    WELL: "Well_order r" and WELL': "Well_order r'"
  shows "embed r (r Osum r') id"
proof-
  have 1: "Well_order (r Osum r')"
    using assms by (auto simp add: Osum_Well_order)
  moreover
  have "compat r (r Osum r') id"
    unfolding compat_def Osum_def by auto
  moreover
  have "inj_on id (Field r)" by simp
  moreover
  have "ofilter (r Osum r') (Field r)"
    using 1 FLD
    by (auto simp add: wo_rel_def wo_rel.ofilter_def Osum_def under_def Field_iff disjoint_iff)
  ultimately show ?thesis
    using assms by (auto simp add: embed_iff_compat_inj_on_ofilter)
qed

corollary Osum_ordLeq:
  assumes FLD: "Field r Int Field r' = {}" and
    WELL: "Well_order r" and WELL': "Well_order r'"
  shows "r \<le>o r Osum r'"
  using assms Osum_embed Osum_Well_order
  unfolding ordLeq_def by blast

lemma Well_order_embed_copy:
  assumes WELL: "well_order_on A r" and
    INJ: "inj_on f A" and SUB: "f ` A \<le> B"
  shows "\<exists>r'. well_order_on B r' \<and> r \<le>o r'"
proof-
  have "bij_betw f A (f ` A)"
    using INJ inj_on_imp_bij_betw by blast
  then obtain r'' where "well_order_on (f ` A) r''" and 1: "r =o r''"
    using WELL  Well_order_iso_copy by blast
  hence 2: "Well_order r'' \<and> Field r'' = (f ` A)"
    using well_order_on_Well_order by blast
      (*  *)
  let ?C = "B - (f ` A)"
  obtain r''' where "well_order_on ?C r'''"
    using well_order_on by blast
  hence 3: "Well_order r''' \<and> Field r''' = ?C"
    using well_order_on_Well_order by blast
      (*  *)
  let ?r' = "r'' Osum r'''"
  have "Field r'' Int Field r''' = {}"
    using 2 3 by auto
  hence "r'' \<le>o ?r'" using Osum_ordLeq[of r'' r'''] 2 3 by blast
  hence 4: "r \<le>o ?r'" using 1 ordIso_ordLeq_trans by blast
      (*  *)
  hence "Well_order ?r'" unfolding ordLeq_def by auto
  moreover
  have "Field ?r' = B" using 2 3 SUB by (auto simp add: Field_Osum)
  ultimately show ?thesis using 4 by blast
qed


subsection \<open>The maxim among a finite set of ordinals\<close>

text \<open>The correct phrasing would be ``a maxim of ...", as \<open>\<le>o\<close> is only a preorder.\<close>

definition isOmax :: "'a rel set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where
    "isOmax  R r \<equiv> r \<in> R \<and> (\<forall>r' \<in> R. r' \<le>o r)"

definition omax :: "'a rel set \<Rightarrow> 'a rel"
  where
    "omax R == SOME r. isOmax R r"

lemma exists_isOmax:
  assumes "finite R" and "R \<noteq> {}" and "\<forall> r \<in> R. Well_order r"
  shows "\<exists> r. isOmax R r"
proof-
  have "finite R \<Longrightarrow> R \<noteq> {} \<longrightarrow> (\<forall> r \<in> R. Well_order r) \<longrightarrow> (\<exists> r. isOmax R r)"
    apply(erule finite_induct) apply(simp add: isOmax_def)
  proof(clarsimp)
    fix r :: "('a \<times> 'a) set" and R assume *: "finite R" and **: "r \<notin> R"
      and ***: "Well_order r" and ****: "\<forall>r\<in>R. Well_order r"
      and IH: "R \<noteq> {} \<longrightarrow> (\<exists>p. isOmax R p)"
    let ?R' = "insert r R"
    show "\<exists>p'. (isOmax ?R' p')"
    proof(cases "R = {}")
      case True
      thus ?thesis
        by (simp add: "***" isOmax_def ordLeq_reflexive)
    next
      case False
      then obtain p where p: "isOmax R p" using IH by auto
      hence  "Well_order p" using **** unfolding isOmax_def by simp
      then consider  "r \<le>o p" | "p \<le>o r"
        using *** ordLeq_total by auto
      then show ?thesis 
      proof cases
        case 1
        then show ?thesis
         using p unfolding isOmax_def by auto
      next
        case 2
        then show ?thesis
          by (metis "***" insert_iff isOmax_def ordLeq_reflexive ordLeq_transitive p)
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

lemma omax_isOmax:
  assumes "finite R" and "R \<noteq> {}" and "\<forall> r \<in> R. Well_order r"
  shows "isOmax R (omax R)"
  unfolding omax_def using assms
  by(simp add: exists_isOmax someI_ex)

lemma omax_in:
  assumes "finite R" and "R \<noteq> {}" and "\<forall> r \<in> R. Well_order r"
  shows "omax R \<in> R"
  using assms omax_isOmax unfolding isOmax_def by blast

lemma Well_order_omax:
  assumes "finite R" and "R \<noteq> {}" and "\<forall>r\<in>R. Well_order r"
  shows "Well_order (omax R)"
  using assms omax_in by blast

lemma omax_maxim:
  assumes "finite R" and "\<forall> r \<in> R. Well_order r" and "r \<in> R"
  shows "r \<le>o omax R"
  using assms omax_isOmax unfolding isOmax_def by blast

lemma omax_ordLeq:
  assumes "finite R" and "R \<noteq> {}" and "\<forall> r \<in> R. r \<le>o p"
  shows "omax R \<le>o p"
  by (meson assms omax_in ordLeq_Well_order_simp)

lemma omax_ordLess:
  assumes "finite R" and "R \<noteq> {}" and "\<forall> r \<in> R. r <o p"
  shows "omax R <o p"
  by (meson assms omax_in ordLess_Well_order_simp)

lemma omax_ordLeq_elim:
  assumes "finite R" and "\<forall> r \<in> R. Well_order r"
    and "omax R \<le>o p" and "r \<in> R"
  shows "r \<le>o p"
  by (meson assms omax_maxim ordLeq_transitive)

lemma omax_ordLess_elim:
  assumes "finite R" and "\<forall> r \<in> R. Well_order r"
    and "omax R <o p" and "r \<in> R"
  shows "r <o p"
  by (meson assms omax_maxim ordLeq_ordLess_trans)

lemma ordLeq_omax:
  assumes "finite R" and "\<forall> r \<in> R. Well_order r"
    and "r \<in> R" and "p \<le>o r"
  shows "p \<le>o omax R"
  by (meson assms omax_maxim ordLeq_transitive)

lemma ordLess_omax:
  assumes "finite R" and "\<forall> r \<in> R. Well_order r"
    and "r \<in> R" and "p <o r"
  shows "p <o omax R"
  by (meson assms omax_maxim ordLess_ordLeq_trans)

lemma omax_ordLeq_mono:
  assumes P: "finite P" and R: "finite R"
    and NE_P: "P \<noteq> {}" and Well_R: "\<forall> r \<in> R. Well_order r"
    and LEQ: "\<forall> p \<in> P. \<exists> r \<in> R. p \<le>o r"
  shows "omax P \<le>o omax R"
  by (meson LEQ NE_P P R Well_R omax_ordLeq ordLeq_omax)

lemma omax_ordLess_mono:
  assumes P: "finite P" and R: "finite R"
    and NE_P: "P \<noteq> {}" and Well_R: "\<forall> r \<in> R. Well_order r"
    and LEQ: "\<forall> p \<in> P. \<exists> r \<in> R. p <o r"
  shows "omax P <o omax R"
  by (meson LEQ NE_P P R Well_R omax_ordLess ordLess_omax)


subsection \<open>Limit and succesor ordinals\<close>

lemma embed_underS2:
  assumes r: "Well_order r" and g: "embed r s g" and a: "a \<in> Field r"
  shows "g ` underS r a = underS s (g a)"
  by (meson a bij_betw_def embed_underS g r)

lemma bij_betw_insert:
  assumes "b \<notin> A" and "f b \<notin> A'" and "bij_betw f A A'"
  shows "bij_betw f (insert b A) (insert (f b) A')"
  using notIn_Un_bij_betw[OF assms] by auto

context wo_rel
begin

lemma underS_induct:
  assumes "\<And>a. (\<And> a1. a1 \<in> underS a \<Longrightarrow> P a1) \<Longrightarrow> P a"
  shows "P a"
  by (induct rule: well_order_induct) (rule assms, simp add: underS_def)

lemma suc_underS:
  assumes B: "B \<subseteq> Field r" and A: "AboveS B \<noteq> {}" and b: "b \<in> B"
  shows "b \<in> underS (suc B)"
  using suc_AboveS[OF B A] b unfolding underS_def AboveS_def by auto

lemma underS_supr:
  assumes bA: "b \<in> underS (supr A)" and A: "A \<subseteq> Field r"
  shows "\<exists> a \<in> A. b \<in> underS a"
proof(rule ccontr, simp)
  have bb: "b \<in> Field r" using bA unfolding underS_def Field_def by auto
  assume "\<forall>a\<in>A.  b \<notin> underS a"
  hence 0: "\<forall>a \<in> A. (a,b) \<in> r" using A bA unfolding underS_def
    by simp (metis REFL in_mono max2_def max2_greater refl_on_domain)
  have "(supr A, b) \<in> r"
    by (simp add: "0" A bb supr_least)
  thus False
    by (metis antisymD bA underS_E wo_rel.ANTISYM wo_rel_axioms)
qed

lemma underS_suc:
  assumes bA: "b \<in> underS (suc A)" and A: "A \<subseteq> Field r"
  shows "\<exists> a \<in> A. b \<in> under a"
proof(rule ccontr, simp)
  have bb: "b \<in> Field r" using bA unfolding underS_def Field_def by auto
  assume "\<forall>a\<in>A.  b \<notin> under a"
  hence 0: "\<forall>a \<in> A. a \<in> underS b" using A bA
    by (metis bb in_mono max2_def max2_greater mem_Collect_eq underS_I under_def)
  have "(suc A, b) \<in> r"
    by (metis "0" A bb suc_least underS_E)
  thus False
    by (metis antisymD bA underS_E wo_rel.ANTISYM wo_rel_axioms)
qed

lemma (in wo_rel) in_underS_supr:
  assumes "j \<in> underS i" and "i \<in> A" and "A \<subseteq> Field r" and "Above A \<noteq> {}"
  shows "j \<in> underS (supr A)"
  by (meson assms LIN in_mono supr_greater supr_inField underS_incl_iff)

lemma inj_on_Field:
  assumes A: "A \<subseteq> Field r" and f: "\<And> a b. \<lbrakk>a \<in> A; b \<in> A; a \<in> underS b\<rbrakk> \<Longrightarrow> f a \<noteq> f b"
  shows "inj_on f A"
  by (smt (verit) A f in_notinI inj_on_def subsetD underS_I)

lemma ofilter_init_seg_of:
  assumes "ofilter F"
  shows "Restr r F initial_segment_of r"
  using assms unfolding ofilter_def init_seg_of_def under_def by auto

lemma underS_init_seg_of_Collect:
  assumes "\<And>j1 j2. \<lbrakk>j2 \<in> underS i; (j1, j2) \<in> r\<rbrakk> \<Longrightarrow> R j1 initial_segment_of R j2"
  shows "{R j |j. j \<in> underS i} \<in> Chains init_seg_of"
  using TOTALS assms 
  by (clarsimp simp: Chains_def) (meson BNF_Least_Fixpoint.underS_Field)

lemma (in wo_rel) Field_init_seg_of_Collect:
  assumes "\<And>j1 j2. \<lbrakk>j2 \<in> Field r; (j1, j2) \<in> r\<rbrakk> \<Longrightarrow> R j1 initial_segment_of R j2"
  shows "{R j |j. j \<in> Field r} \<in> Chains init_seg_of"
  using TOTALS assms by (auto simp: Chains_def)

subsubsection \<open>Successor and limit elements of an ordinal\<close>

definition "succ i \<equiv> suc {i}"

definition "isSucc i \<equiv> \<exists> j. aboveS j \<noteq> {} \<and> i = succ j"

definition "zero = minim (Field r)"

definition "isLim i \<equiv> \<not> isSucc i"

lemma zero_smallest[simp]:
  assumes "j \<in> Field r" shows "(zero, j) \<in> r"
  by (simp add: assms wo_rel.ofilter_linord wo_rel_axioms zero_def)

lemma zero_in_Field: assumes "Field r \<noteq> {}"  shows "zero \<in> Field r"
  using assms unfolding zero_def by (metis Field_ofilter minim_in ofilter_def)

lemma leq_zero_imp[simp]:
  "(x, zero) \<in> r \<Longrightarrow> x = zero"
  by (metis ANTISYM WELL antisymD well_order_on_domain zero_smallest)

lemma leq_zero[simp]:
  assumes "Field r \<noteq> {}"  shows "(x, zero) \<in> r \<longleftrightarrow> x = zero"
  using zero_in_Field[OF assms] in_notinI[of x zero] by auto

lemma under_zero[simp]:
  assumes "Field r \<noteq> {}" shows "under zero = {zero}"
  using assms unfolding under_def by auto

lemma underS_zero[simp,intro]: "underS zero = {}"
  unfolding underS_def by auto

lemma isSucc_succ: "aboveS i \<noteq> {} \<Longrightarrow> isSucc (succ i)"
  unfolding isSucc_def succ_def by auto

lemma succ_in_diff:
  assumes "aboveS i \<noteq> {}"  shows "(i,succ i) \<in> r \<and> succ i \<noteq> i"
  using assms suc_greater[of "{i}"] unfolding succ_def AboveS_def aboveS_def Field_def by auto

lemmas succ_in[simp] = succ_in_diff[THEN conjunct1]
lemmas succ_diff[simp] = succ_in_diff[THEN conjunct2]

lemma succ_in_Field[simp]:
  assumes "aboveS i \<noteq> {}"  shows "succ i \<in> Field r"
  using succ_in[OF assms] unfolding Field_def by auto

lemma succ_not_in:
  assumes "aboveS i \<noteq> {}" shows "(succ i, i) \<notin> r"
  by (metis FieldI2 assms max2_equals1 max2_equals2 succ_diff succ_in)

lemma not_isSucc_zero: "\<not> isSucc zero"
  by (metis isSucc_def leq_zero_imp succ_in_diff)

lemma isLim_zero[simp]: "isLim zero"
  by (metis isLim_def not_isSucc_zero)

lemma succ_smallest:
  assumes "(i,j) \<in> r" and "i \<noteq> j"
  shows "(succ i, j) \<in> r"
  by (metis Field_iff assms empty_subsetI insert_subset singletonD suc_least succ_def)

lemma isLim_supr:
  assumes f: "i \<in> Field r" and l: "isLim i"
  shows "i = supr (underS i)"
proof(rule equals_supr)
  fix j assume j: "j \<in> Field r" and 1: "\<And> j'. j' \<in> underS i \<Longrightarrow> (j',j) \<in> r"
  show "(i,j) \<in> r" 
  proof(intro in_notinI[OF _ f j], safe)
    assume ji: "(j,i) \<in> r" "j \<noteq> i"
    hence a: "aboveS j \<noteq> {}" unfolding aboveS_def by auto
    hence "i \<noteq> succ j" using l unfolding isLim_def isSucc_def by auto
    moreover have "(succ j, i) \<in> r" using succ_smallest[OF ji] by auto
    ultimately have "succ j \<in> underS i" unfolding underS_def by auto
    hence "(succ j, j) \<in> r" using 1 by auto
    thus False using succ_not_in[OF a] by simp
  qed
qed(use f underS_def Field_def in fastforce)+

definition "pred i \<equiv> SOME j. j \<in> Field r \<and> aboveS j \<noteq> {} \<and> succ j = i"

lemma pred_Field_succ:
  assumes "isSucc i" shows "pred i \<in> Field r \<and> aboveS (pred i) \<noteq> {} \<and> succ (pred i) = i"
proof-
  obtain j where j: "aboveS j \<noteq> {}" "i = succ j" 
    using assms unfolding isSucc_def by auto
  then obtain "j \<in> Field r" "j \<noteq> i"
    by (metis FieldI1 succ_diff succ_in)
  then show ?thesis unfolding pred_def
    by (metis (mono_tags, lifting) j someI_ex)
qed

lemmas pred_Field[simp] = pred_Field_succ[THEN conjunct1]
lemmas aboveS_pred[simp] = pred_Field_succ[THEN conjunct2, THEN conjunct1]
lemmas succ_pred[simp] = pred_Field_succ[THEN conjunct2, THEN conjunct2]

lemma isSucc_pred_in:
  assumes "isSucc i"  shows "(pred i, i) \<in> r"
  by (metis assms pred_Field_succ succ_in)

lemma isSucc_pred_diff:
  assumes "isSucc i"  shows "pred i \<noteq> i"
  by (metis aboveS_pred assms succ_diff succ_pred)

(* todo: pred maximal, pred injective? *)

lemma succ_inj[simp]:
  assumes "aboveS i \<noteq> {}" and "aboveS j \<noteq> {}"
  shows "succ i = succ j \<longleftrightarrow> i = j"
  by (metis FieldI1 assms succ_def succ_in supr_under under_underS_suc)

lemma pred_succ[simp]:
  assumes "aboveS j \<noteq> {}"  shows "pred (succ j) = j"
  using assms isSucc_def pred_Field_succ succ_inj by blast

lemma less_succ[simp]:
  assumes "aboveS i \<noteq> {}"
  shows "(j, succ i) \<in> r \<longleftrightarrow> (j,i) \<in> r \<or> j = succ i"
  by (metis FieldI1 assms in_notinI max2_equals1 max2_equals2 max2_iff succ_in succ_smallest)

lemma underS_succ[simp]:
  assumes "aboveS i \<noteq> {}"
  shows "underS (succ i) = under i"
  unfolding underS_def under_def by (auto simp: assms succ_not_in)

lemma succ_mono:
  assumes "aboveS j \<noteq> {}" and "(i,j) \<in> r"
  shows "(succ i, succ j) \<in> r"
  by (metis (full_types) assms less_succ succ_smallest)

lemma under_succ[simp]:
  assumes "aboveS i \<noteq> {}"
  shows "under (succ i) = insert (succ i) (under i)"
  using less_succ[OF assms] unfolding under_def by auto

definition mergeSL :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where
    "mergeSL S L f i \<equiv> if isSucc i then S (pred i) (f (pred i)) else L f i"


subsubsection \<open>Well-order recursion with (zero), succesor, and limit\<close>

definition worecSL :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "worecSL S L \<equiv> worec (mergeSL S L)"

definition "adm_woL L \<equiv> \<forall>f g i. isLim i \<and> (\<forall>j\<in>underS i. f j = g j) \<longrightarrow> L f i = L g i"

lemma mergeSL: "adm_woL L \<Longrightarrow>adm_wo (mergeSL S L)"
  unfolding adm_wo_def adm_woL_def isLim_def
  by (smt (verit, ccfv_threshold) isSucc_pred_diff isSucc_pred_in mergeSL_def underS_I)

lemma worec_fixpoint1: "adm_wo H \<Longrightarrow> worec H i = H (worec H) i"
  by (metis worec_fixpoint)

lemma worecSL_isSucc:
  assumes a: "adm_woL L" and i: "isSucc i"
  shows "worecSL S L i = S (pred i) (worecSL S L (pred i))"
  by (metis a i mergeSL mergeSL_def worecSL_def worec_fixpoint)

lemma worecSL_succ:
  assumes a: "adm_woL L" and i: "aboveS j \<noteq> {}"
  shows "worecSL S L (succ j) = S j (worecSL S L j)"
  by (simp add: a i isSucc_succ worecSL_isSucc)

lemma worecSL_isLim:
  assumes a: "adm_woL L" and i: "isLim i"
  shows "worecSL S L i = L (worecSL S L) i"
  by (metis a i isLim_def mergeSL mergeSL_def worecSL_def worec_fixpoint)

definition worecZSL :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "worecZSL Z S L \<equiv> worecSL S (\<lambda> f a. if a = zero then Z else L f a)"

lemma worecZSL_zero:
  assumes a: "adm_woL L"
  shows "worecZSL Z S L zero = Z"
  by (smt (verit, best) adm_woL_def assms isLim_zero worecSL_isLim worecZSL_def)

lemma worecZSL_succ:
  assumes a: "adm_woL L" and i: "aboveS j \<noteq> {}"
  shows "worecZSL Z S L (succ j) = S j (worecZSL Z S L j)"
  unfolding worecZSL_def
  by (smt (verit, best) a adm_woL_def i worecSL_succ)

lemma worecZSL_isLim:
  assumes a: "adm_woL L" and "isLim i" and "i \<noteq> zero"
  shows "worecZSL Z S L i = L (worecZSL Z S L) i"
proof-
  let ?L = "\<lambda> f a. if a = zero then Z else L f a"
  have "worecZSL Z S L i = ?L (worecZSL Z S L) i"
    unfolding worecZSL_def by (smt (verit, best) adm_woL_def assms worecSL_isLim)
  also have "\<dots> = L (worecZSL Z S L) i" using assms by simp
  finally show ?thesis .
qed


subsubsection \<open>Well-order succ-lim induction\<close>

lemma ord_cases:
  obtains j where "i = succ j" and "aboveS j \<noteq> {}"  | "isLim i"
  by (metis isLim_def isSucc_def)

lemma well_order_inductSL[case_names Suc Lim]:
  assumes "\<And>i. \<lbrakk>aboveS i \<noteq> {}; P i\<rbrakk> \<Longrightarrow> P (succ i)"  "\<And>i. \<lbrakk>isLim i; \<And>j. j \<in> underS i \<Longrightarrow> P j\<rbrakk> \<Longrightarrow> P i"
  shows "P i"
proof(induction rule: well_order_induct)
  case (1 x)
  then show ?case     
    by (metis assms ord_cases succ_diff succ_in underS_E)
qed

lemma well_order_inductZSL[case_names Zero Suc Lim]:
  assumes "P zero"
    and  "\<And>i. \<lbrakk>aboveS i \<noteq> {}; P i\<rbrakk> \<Longrightarrow> P (succ i)" and
    "\<And>i. \<lbrakk>isLim i; i \<noteq> zero; \<And>j. j \<in> underS i \<Longrightarrow> P j\<rbrakk> \<Longrightarrow> P i"
  shows "P i"
  by (metis assms well_order_inductSL)

(* Succesor and limit ordinals *)
definition "isSuccOrd \<equiv> \<exists> j \<in> Field r. \<forall> i \<in> Field r. (i,j) \<in> r"
definition "isLimOrd \<equiv> \<not> isSuccOrd"

lemma isLimOrd_succ:
  assumes isLimOrd and "i \<in> Field r"
  shows "succ i \<in> Field r"
  using assms unfolding isLimOrd_def isSuccOrd_def
  by (metis REFL in_notinI refl_on_domain succ_smallest)

lemma isLimOrd_aboveS:
  assumes l: isLimOrd and i: "i \<in> Field r"
  shows "aboveS i \<noteq> {}"
proof-
  obtain j where "j \<in> Field r" and "(j,i) \<notin> r"
    using assms unfolding isLimOrd_def isSuccOrd_def by auto
  hence "(i,j) \<in> r \<and> j \<noteq> i" by (metis i max2_def max2_greater)
  thus ?thesis unfolding aboveS_def by auto
qed

lemma succ_aboveS_isLimOrd:
  assumes "\<forall> i \<in> Field r. aboveS i \<noteq> {} \<and> succ i \<in> Field r"
  shows isLimOrd
  using assms isLimOrd_def isSuccOrd_def succ_not_in by blast

lemma isLim_iff:
  assumes l: "isLim i" and j: "j \<in> underS i"
  shows "\<exists> k. k \<in> underS i \<and> j \<in> underS k"
  by (metis Order_Relation.underS_Field empty_iff isLim_supr j l underS_empty underS_supr)

end (* context wo_rel *)

abbreviation "zero \<equiv> wo_rel.zero"
abbreviation "succ \<equiv> wo_rel.succ"
abbreviation "pred \<equiv> wo_rel.pred"
abbreviation "isSucc \<equiv> wo_rel.isSucc"
abbreviation "isLim \<equiv> wo_rel.isLim"
abbreviation "isLimOrd \<equiv> wo_rel.isLimOrd"
abbreviation "isSuccOrd \<equiv> wo_rel.isSuccOrd"
abbreviation "adm_woL \<equiv> wo_rel.adm_woL"
abbreviation "worecSL \<equiv> wo_rel.worecSL"
abbreviation "worecZSL \<equiv> wo_rel.worecZSL"


subsection \<open>Projections of wellorders\<close>

definition "oproj r s f \<equiv> Field s \<subseteq> f ` (Field r) \<and> compat r s f"

lemma oproj_in:
  assumes "oproj r s f" and "(a,a') \<in> r"
  shows "(f a, f a') \<in> s"
  using assms unfolding oproj_def compat_def by auto

lemma oproj_Field:
  assumes f: "oproj r s f" and a: "a \<in> Field r"
  shows "f a \<in> Field s"
  using oproj_in[OF f] a unfolding Field_def by auto

lemma oproj_Field2:
  assumes f: "oproj r s f" and a: "b \<in> Field s"
  shows "\<exists> a \<in> Field r. f a = b"
  using assms unfolding oproj_def by auto

lemma oproj_under:
  assumes f:  "oproj r s f" and a: "a \<in> under r a'"
  shows "f a \<in> under s (f a')"
  using oproj_in[OF f] a unfolding under_def by auto

(* An ordinal is embedded in another whenever it is embedded as an order
(not necessarily as initial segment):*)
theorem embedI:
  assumes r: "Well_order r" and s: "Well_order s"
    and f: "\<And> a. a \<in> Field r \<Longrightarrow> f a \<in> Field s \<and> f ` underS r a \<subseteq> underS s (f a)"
  shows "\<exists> g. embed r s g"
proof-
  interpret r: wo_rel r by unfold_locales (rule r)
  interpret s: wo_rel s by unfold_locales (rule s)
  let ?G = "\<lambda> g a. suc s (g ` underS r a)"
  define g where "g = worec r ?G"
  have adm: "adm_wo r ?G" unfolding r.adm_wo_def image_def by auto
      (*  *)
  {fix a assume "a \<in> Field r"
    hence "bij_betw g (under r a) (under s (g a)) \<and>
          g a \<in> under s (f a)"
    proof(induction a rule: r.underS_induct)
      case (1 a)
      hence a: "a \<in> Field r"
        and IH1a: "\<And> a1. a1 \<in> underS r a \<Longrightarrow> inj_on g (under r a1)"
        and IH1b: "\<And> a1. a1 \<in> underS r a \<Longrightarrow> g ` under r a1 = under s (g a1)"
        and IH2: "\<And> a1. a1 \<in> underS r a \<Longrightarrow> g a1 \<in> under s (f a1)"
        unfolding underS_def Field_def bij_betw_def by auto
      have fa: "f a \<in> Field s" using f[OF a] by auto
      have g: "g a = suc s (g ` underS r a)"
        using r.worec_fixpoint[OF adm] unfolding g_def fun_eq_iff by blast
      have A0: "g ` underS r a \<subseteq> Field s"
        using IH1b by (metis IH2 image_subsetI in_mono under_Field)
      {fix a1 assume a1: "a1 \<in> underS r a"
        from IH2[OF this] have "g a1 \<in> under s (f a1)" .
        moreover have "f a1 \<in> underS s (f a)" using f[OF a] a1 by auto
        ultimately have "g a1 \<in> underS s (f a)" by (metis s.ANTISYM s.TRANS under_underS_trans)
      }
      hence fa_in: "f a \<in> AboveS s (g ` underS r a)" unfolding AboveS_def
        using fa by simp (metis (lifting, full_types) mem_Collect_eq underS_def)
      hence A: "AboveS s (g ` underS r a) \<noteq> {}" by auto
      have ga: "g a \<in> Field s" unfolding g using s.suc_inField[OF A0 A] .
      show ?case
        unfolding bij_betw_def
      proof (intro conjI)
        show "inj_on g (r.under a)"
          by (metis A IH1a IH1b a bij_betw_def g ga r s s.suc_greater subsetI wellorders_totally_ordered_aux)
        show "g ` r.under a = s.under (g a)"
          by (metis A A0 IH1a IH1b a bij_betw_def g ga r s s.suc_greater wellorders_totally_ordered_aux)
        show "g a \<in> s.under (f a)"
          by (simp add: fa_in g s.suc_least_AboveS under_def)
      qed
    qed
  }
  thus ?thesis unfolding embed_def by auto
qed

corollary ordLeq_def2:
  "r \<le>o s \<longleftrightarrow> Well_order r \<and> Well_order s \<and>
               (\<exists> f. \<forall> a \<in> Field r. f a \<in> Field s \<and> f ` underS r a \<subseteq> underS s (f a))"
  using embed_in_Field[of r s] embed_underS2[of r s] embedI[of r s]
  unfolding ordLeq_def by fast

lemma iso_oproj:
  assumes r: "Well_order r" and s: "Well_order s" and f: "iso r s f"
  shows "oproj r s f"
  by (metis embed_Field f iso_Field iso_iff iso_iff3 oproj_def r s)

theorem oproj_embed:
  assumes r: "Well_order r" and s: "Well_order s" and f: "oproj r s f"
  shows "\<exists> g. embed s r g"
proof (rule embedI[OF s r, of "inv_into (Field r) f"], unfold underS_def, safe)
  fix b assume "b \<in> Field s"
  thus "inv_into (Field r) f b \<in> Field r" 
    using oproj_Field2[OF f] by (metis imageI inv_into_into)
next
  fix a b assume "b \<in> Field s" "a \<noteq> b" "(a, b) \<in> s"
    "inv_into (Field r) f a = inv_into (Field r) f b"
  with f show False
    by (meson FieldI1 in_mono inv_into_injective oproj_def)
next
  fix a b assume *: "b \<in> Field s" "a \<noteq> b" "(a, b) \<in> s"
  { assume notin: "(inv_into (Field r) f a, inv_into (Field r) f b) \<notin> r"
    moreover
    from *(3) have "a \<in> Field s" unfolding Field_def by auto
    then have "(inv_into (Field r) f b, inv_into (Field r) f a) \<in> r"
      by (meson "*"(1) notin f in_mono inv_into_into oproj_def r wo_rel.in_notinI wo_rel.intro)
    ultimately have "(inv_into (Field r) f b, inv_into (Field r) f a) \<in> r"
      using r by (auto simp: well_order_on_def linear_order_on_def total_on_def)
    with f[unfolded oproj_def compat_def] *(1) \<open>a \<in> Field s\<close>
      f_inv_into_f[of b f "Field r"] f_inv_into_f[of a f "Field r"]
    have "(b, a) \<in> s" by (metis in_mono)
    with *(2,3) s have False
      by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def antisym_def)
  } thus "(inv_into (Field r) f a, inv_into (Field r) f b) \<in> r" by blast
qed

corollary oproj_ordLeq:
  assumes r: "Well_order r" and s: "Well_order s" and f: "oproj r s f"
  shows "s \<le>o r"
  using f oproj_embed ordLess_iff ordLess_or_ordLeq r s by blast

end
