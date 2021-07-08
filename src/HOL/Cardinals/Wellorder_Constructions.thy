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

lemma Func_emp2[simp]: "A \<noteq> {} \<Longrightarrow> Func A {} = {}" by auto


subsection \<open>Restriction to a set\<close>

lemma Restr_incr2:
"r <= r' \<Longrightarrow> Restr r A <= Restr r' A"
by blast

lemma Restr_incr:
"\<lbrakk>r \<le> r'; A \<le> A'\<rbrakk> \<Longrightarrow> Restr r A \<le> Restr r' A'"
by blast

lemma Restr_Int:
"Restr (Restr r A) B = Restr r (A Int B)"
by blast

lemma Restr_iff: "(a,b) \<in> Restr r A = (a \<in> A \<and> b \<in> A \<and> (a,b) \<in> r)"
by (auto simp add: Field_def)

lemma Restr_subset1: "Restr r A \<le> r"
by auto

lemma Restr_subset2: "Restr r A \<le> A \<times> A"
by auto

lemma wf_Restr:
"wf r \<Longrightarrow> wf(Restr r A)"
using Restr_subset by (elim wf_subset) simp

lemma Restr_incr1:
"A \<le> B \<Longrightarrow> Restr r A \<le> Restr r B"
by blast


subsection \<open>Order filters versus restrictions and embeddings\<close>

lemma ofilter_Restr:
assumes WELL: "Well_order r" and
        OFA: "ofilter r A" and OFB: "ofilter r B" and SUB: "A \<le> B"
shows "ofilter (Restr r B) A"
proof-
  let ?rB = "Restr r B"
  have Well: "wo_rel r" unfolding wo_rel_def using WELL .
  hence Refl: "Refl r" by (auto simp add: wo_rel.REFL)
  hence Field: "Field ?rB = Field r Int B"
  using Refl_Field_Restr by blast
  have WellB: "wo_rel ?rB \<and> Well_order ?rB" using WELL
  by (auto simp add: Well_order_Restr wo_rel_def)
  (* Main proof *)
  show ?thesis
  proof(auto simp add: WellB wo_rel.ofilter_def)
    fix a assume "a \<in> A"
    hence "a \<in> Field r \<and> a \<in> B" using assms Well
    by (auto simp add: wo_rel.ofilter_def)
    with Field show "a \<in> Field(Restr r B)" by auto
  next
    fix a b assume *: "a \<in> A"  and "b \<in> under (Restr r B) a"
    hence "b \<in> under r a"
    using WELL OFB SUB ofilter_Restr_under[of r B a] by auto
    thus "b \<in> A" using * Well OFA by(auto simp add: wo_rel.ofilter_def)
  qed
qed

lemma ofilter_subset_iso:
assumes WELL: "Well_order r" and
        OFA: "ofilter r A" and OFB: "ofilter r B"
shows "(A = B) = iso (Restr r A) (Restr r B) id"
using assms
by (auto simp add: ofilter_subset_embedS_iso)


subsection \<open>Ordering the well-orders by existence of embeddings\<close>

corollary ordLeq_refl_on: "refl_on {r. Well_order r} ordLeq"
using ordLeq_reflexive unfolding ordLeq_def refl_on_def
by blast

corollary ordLeq_trans: "trans ordLeq"
using trans_def[of ordLeq] ordLeq_transitive by blast

corollary ordLeq_preorder_on: "preorder_on {r. Well_order r} ordLeq"
by(auto simp add: preorder_on_def ordLeq_refl_on ordLeq_trans)

corollary ordIso_refl_on: "refl_on {r. Well_order r} ordIso"
using ordIso_reflexive unfolding refl_on_def ordIso_def
by blast

corollary ordIso_trans: "trans ordIso"
using trans_def[of ordIso] ordIso_transitive by blast

corollary ordIso_sym: "sym ordIso"
by (auto simp add: sym_def ordIso_symmetric)

corollary ordIso_equiv: "equiv {r. Well_order r} ordIso"
by (auto simp add:  equiv_def ordIso_sym ordIso_refl_on ordIso_trans)

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

lemma not_ordLeq_ordLess:
"r \<le>o r' \<Longrightarrow> \<not> r' <o r"
using not_ordLess_ordLeq by blast

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
proof-
  have "A \<le> Field r" using assms by (auto simp add: wo_rel_def wo_rel.ofilter_def)
  thus ?thesis using assms
  by (simp add: ofilter_subset_ordLeq wo_rel.Field_ofilter
      wo_rel_def Restr_Field)
qed

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
  proof(clarify)
    fix a' b'
    assume "(a',b') \<in> dir_image r1 f" "(a',b') \<in> dir_image r2 f"
    then obtain a1 b1 a2 b2
    where 1: "a' = f a1 \<and> b' = f b1 \<and> a' = f a2 \<and> b' = f b2" and
          2: "(a1,b1) \<in> r1 \<and> (a2,b2) \<in> r2" and
          3: "{a1,b1} \<le> Field r1 \<and> {a2,b2} \<le> Field r2"
    unfolding dir_image_def Field_def by blast
    hence "a1 = a2 \<and> b1 = b2" using assms unfolding inj_on_def by auto
    hence "a' = f a1 \<and> b' = f b1 \<and> (a1,b1) \<in> r1 Int r2 \<and> (a2,b2) \<in> r1 Int r2"
    using 1 2 by auto
    thus "(a',b') \<in> dir_image (r1 \<inter> r2) f"
    unfolding dir_image_def by blast
  qed
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
  using 1 proof(auto simp add: wo_rel_def wo_rel.ofilter_def
                               Field_Osum under_def)
    fix a b assume 2: "a \<in> Field r" and 3: "(b,a) \<in> r Osum r'"
    moreover
    {assume "(b,a) \<in> r'"
     hence "a \<in> Field r'" using Field_def[of r'] by blast
     hence False using 2 FLD by blast
    }
    moreover
    {assume "a \<in> Field r'"
     hence False using 2 FLD by blast
    }
    ultimately
    show "b \<in> Field r" by (auto simp add: Osum_def Field_def)
  qed
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
      assume Case1: "R = {}"
      thus ?thesis unfolding isOmax_def using ***
      by (simp add: ordLeq_reflexive)
    next
      assume Case2: "R \<noteq> {}"
      then obtain p where p: "isOmax R p" using IH by auto
      hence 1: "Well_order p" using **** unfolding isOmax_def by simp
      {assume Case21: "r \<le>o p"
       hence "isOmax ?R' p" using p unfolding isOmax_def by simp
       hence ?thesis by auto
      }
      moreover
      {assume Case22: "p \<le>o r"
       {fix r' assume "r' \<in> ?R'"
        moreover
        {assume "r' \<in> R"
         hence "r' \<le>o p" using p unfolding isOmax_def by simp
         hence "r' \<le>o r" using Case22 by(rule ordLeq_transitive)
        }
        moreover have "r \<le>o r" using *** by(rule ordLeq_reflexive)
        ultimately have "r' \<le>o r" by auto
       }
       hence "isOmax ?R' r" unfolding isOmax_def by simp
       hence ?thesis by auto
      }
      moreover have "r \<le>o p \<or> p \<le>o r"
      using 1 *** ordLeq_total by auto
      ultimately show ?thesis by blast
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
using assms apply - apply(drule omax_in) by auto

lemma omax_maxim:
assumes "finite R" and "\<forall> r \<in> R. Well_order r" and "r \<in> R"
shows "r \<le>o omax R"
using assms omax_isOmax unfolding isOmax_def by blast

lemma omax_ordLeq:
assumes "finite R" and "R \<noteq> {}" and *: "\<forall> r \<in> R. r \<le>o p"
shows "omax R \<le>o p"
proof-
  have "\<forall> r \<in> R. Well_order r" using * unfolding ordLeq_def by simp
  thus ?thesis using assms omax_in by auto
qed

lemma omax_ordLess:
assumes "finite R" and "R \<noteq> {}" and *: "\<forall> r \<in> R. r <o p"
shows "omax R <o p"
proof-
  have "\<forall> r \<in> R. Well_order r" using * unfolding ordLess_def by simp
  thus ?thesis using assms omax_in by auto
qed

lemma omax_ordLeq_elim:
assumes "finite R" and "\<forall> r \<in> R. Well_order r"
and "omax R \<le>o p" and "r \<in> R"
shows "r \<le>o p"
using assms omax_maxim[of R r] apply simp
using ordLeq_transitive by blast

lemma omax_ordLess_elim:
assumes "finite R" and "\<forall> r \<in> R. Well_order r"
and "omax R <o p" and "r \<in> R"
shows "r <o p"
using assms omax_maxim[of R r] apply simp
using ordLeq_ordLess_trans by blast

lemma ordLeq_omax:
assumes "finite R" and "\<forall> r \<in> R. Well_order r"
and "r \<in> R" and "p \<le>o r"
shows "p \<le>o omax R"
using assms omax_maxim[of R r] apply simp
using ordLeq_transitive by blast

lemma ordLess_omax:
assumes "finite R" and "\<forall> r \<in> R. Well_order r"
and "r \<in> R" and "p <o r"
shows "p <o omax R"
using assms omax_maxim[of R r] apply simp
using ordLess_ordLeq_trans by blast

lemma omax_ordLeq_mono:
assumes P: "finite P" and R: "finite R"
and NE_P: "P \<noteq> {}" and Well_R: "\<forall> r \<in> R. Well_order r"
and LEQ: "\<forall> p \<in> P. \<exists> r \<in> R. p \<le>o r"
shows "omax P \<le>o omax R"
proof-
  let ?mp = "omax P"  let ?mr = "omax R"
  {fix p assume "p \<in> P"
   then obtain r where r: "r \<in> R" and "p \<le>o r"
   using LEQ by blast
   moreover have "r <=o ?mr"
   using r R Well_R omax_maxim by blast
   ultimately have "p <=o ?mr"
   using ordLeq_transitive by blast
  }
  thus "?mp <=o ?mr"
  using NE_P P using omax_ordLeq by blast
qed

lemma omax_ordLess_mono:
assumes P: "finite P" and R: "finite R"
and NE_P: "P \<noteq> {}" and Well_R: "\<forall> r \<in> R. Well_order r"
and LEQ: "\<forall> p \<in> P. \<exists> r \<in> R. p <o r"
shows "omax P <o omax R"
proof-
  let ?mp = "omax P"  let ?mr = "omax R"
  {fix p assume "p \<in> P"
   then obtain r where r: "r \<in> R" and "p <o r"
   using LEQ by blast
   moreover have "r <=o ?mr"
   using r R Well_R omax_maxim by blast
   ultimately have "p <o ?mr"
   using ordLess_ordLeq_trans by blast
  }
  thus "?mp <o ?mr"
  using NE_P P omax_ordLess by blast
qed


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
proof(rule ccontr, auto)
  have bb: "b \<in> Field r" using bA unfolding underS_def Field_def by auto
  assume "\<forall>a\<in>A.  b \<notin> underS a"
  hence 0: "\<forall>a \<in> A. (a,b) \<in> r" using A bA unfolding underS_def
  by simp (metis REFL in_mono max2_def max2_greater refl_on_domain)
  have "(supr A, b) \<in> r" apply(rule supr_least[OF A bb]) using 0 by auto
  thus False using bA unfolding underS_def by simp (metis ANTISYM antisymD)
qed

lemma underS_suc:
assumes bA: "b \<in> underS (suc A)" and A: "A \<subseteq> Field r"
shows "\<exists> a \<in> A. b \<in> under a"
proof(rule ccontr, auto)
  have bb: "b \<in> Field r" using bA unfolding underS_def Field_def by auto
  assume "\<forall>a\<in>A.  b \<notin> under a"
  hence 0: "\<forall>a \<in> A. a \<in> underS b" using A bA unfolding underS_def
  by simp (metis (lifting) bb max2_def max2_greater mem_Collect_eq under_def rev_subsetD)
  have "(suc A, b) \<in> r" apply(rule suc_least[OF A bb]) using 0 unfolding underS_def by auto
  thus False using bA unfolding underS_def by simp (metis ANTISYM antisymD)
qed

lemma (in wo_rel) in_underS_supr:
assumes j: "j \<in> underS i" and i: "i \<in> A" and A: "A \<subseteq> Field r" and AA: "Above A \<noteq> {}"
shows "j \<in> underS (supr A)"
proof-
  have "(i,supr A) \<in> r" using supr_greater[OF A AA i] .
  thus ?thesis using j unfolding underS_def
  by simp (metis REFL TRANS max2_def max2_equals1 refl_on_domain transD)
qed

lemma inj_on_Field:
assumes A: "A \<subseteq> Field r" and f: "\<And> a b. \<lbrakk>a \<in> A; b \<in> A; a \<in> underS b\<rbrakk> \<Longrightarrow> f a \<noteq> f b"
shows "inj_on f A"
unfolding inj_on_def proof safe
  fix a b assume a: "a \<in> A" and b: "b \<in> A" and fab: "f a = f b"
  {assume "a \<in> underS b"
   hence False using f[OF a b] fab by auto
  }
  moreover
  {assume "b \<in> underS a"
   hence False using f[OF b a] fab by auto
  }
  ultimately show "a = b" using TOTALS A a b unfolding underS_def by auto
qed

lemma in_notinI:
assumes "(j,i) \<notin> r \<or> j = i" and "i \<in> Field r" and "j \<in> Field r"
shows "(i,j) \<in> r" by (metis assms max2_def max2_greater_among)

lemma ofilter_init_seg_of:
assumes "ofilter F"
shows "Restr r F initial_segment_of r"
using assms unfolding ofilter_def init_seg_of_def under_def by auto

lemma underS_init_seg_of_Collect:
assumes "\<And>j1 j2. \<lbrakk>j2 \<in> underS i; (j1, j2) \<in> r\<rbrakk> \<Longrightarrow> R j1 initial_segment_of R j2"
shows "{R j |j. j \<in> underS i} \<in> Chains init_seg_of"
unfolding Chains_def proof safe
  fix j ja assume jS: "j \<in> underS i" and jaS: "ja \<in> underS i"
  and init: "(R ja, R j) \<notin> init_seg_of"
  hence jja: "{j,ja} \<subseteq> Field r" and j: "j \<in> Field r" and ja: "ja \<in> Field r"
  and jjai: "(j,i) \<in> r" "(ja,i) \<in> r"
  and i: "i \<notin> {j,ja}" unfolding Field_def underS_def by auto
  have jj: "(j,j) \<in> r" and jaja: "(ja,ja) \<in> r" using j ja by (metis in_notinI)+
  show "R j initial_segment_of R ja"
  using jja init jjai i
  by (elim cases_Total3 disjE) (auto elim: cases_Total3 intro!: assms simp: underS_def)
qed

lemma (in wo_rel) Field_init_seg_of_Collect:
assumes "\<And>j1 j2. \<lbrakk>j2 \<in> Field r; (j1, j2) \<in> r\<rbrakk> \<Longrightarrow> R j1 initial_segment_of R j2"
shows "{R j |j. j \<in> Field r} \<in> Chains init_seg_of"
unfolding Chains_def proof safe
  fix j ja assume jS: "j \<in> Field r" and jaS: "ja \<in> Field r"
  and init: "(R ja, R j) \<notin> init_seg_of"
  hence jja: "{j,ja} \<subseteq> Field r" and j: "j \<in> Field r" and ja: "ja \<in> Field r"
  unfolding Field_def underS_def by auto
  have jj: "(j,j) \<in> r" and jaja: "(ja,ja) \<in> r" using j ja by (metis in_notinI)+
  show "R j initial_segment_of R ja"
  using jja init
  by (elim cases_Total3 disjE) (auto elim: cases_Total3 intro!: assms simp: Field_def)
qed

subsubsection \<open>Successor and limit elements of an ordinal\<close>

definition "succ i \<equiv> suc {i}"

definition "isSucc i \<equiv> \<exists> j. aboveS j \<noteq> {} \<and> i = succ j"

definition "zero = minim (Field r)"

definition "isLim i \<equiv> \<not> isSucc i"

lemma zero_smallest[simp]:
assumes "j \<in> Field r" shows "(zero, j) \<in> r"
unfolding zero_def
by (metis AboveS_Field assms subset_AboveS_UnderS subset_antisym subset_refl suc_def suc_least_AboveS)

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
proof
  assume 1: "(succ i, i) \<in> r"
  hence "succ i \<in> Field r \<and> i \<in> Field r" unfolding Field_def by auto
  hence "(i, succ i) \<in> r \<and> succ i \<noteq> i" using assms by auto
  thus False using 1 by (metis ANTISYM antisymD)
qed

lemma not_isSucc_zero: "\<not> isSucc zero"
proof
  assume *: "isSucc zero"
  then obtain i where "aboveS i \<noteq> {}" and 1: "minim (Field r) = succ i"
  unfolding isSucc_def zero_def by auto
  hence "succ i \<in> Field r" by auto
  with * show False
    by (metis REFL isSucc_def minim_least refl_on_domain
        subset_refl succ_in succ_not_in zero_def)
qed

lemma isLim_zero[simp]: "isLim zero"
  by (metis isLim_def not_isSucc_zero)

lemma succ_smallest:
assumes "(i,j) \<in> r" and "i \<noteq> j"
shows "(succ i, j) \<in> r"
unfolding succ_def apply(rule suc_least)
using assms unfolding Field_def by auto

lemma isLim_supr:
assumes f: "i \<in> Field r" and l: "isLim i"
shows "i = supr (underS i)"
proof(rule equals_supr)
  fix j assume j: "j \<in> Field r" and 1: "\<And> j'. j' \<in> underS i \<Longrightarrow> (j',j) \<in> r"
  show "(i,j) \<in> r" proof(intro in_notinI[OF _ f j], safe)
    assume ji: "(j,i) \<in> r" "j \<noteq> i"
    hence a: "aboveS j \<noteq> {}" unfolding aboveS_def by auto
    hence "i \<noteq> succ j" using l unfolding isLim_def isSucc_def by auto
    moreover have "(succ j, i) \<in> r" using succ_smallest[OF ji] by auto
    ultimately have "succ j \<in> underS i" unfolding underS_def by auto
    hence "(succ j, j) \<in> r" using 1 by auto
    thus False using succ_not_in[OF a] by simp
  qed
qed(insert f, unfold underS_def Field_def, auto)

definition "pred i \<equiv> SOME j. j \<in> Field r \<and> aboveS j \<noteq> {} \<and> succ j = i"

lemma pred_Field_succ:
assumes "isSucc i" shows "pred i \<in> Field r \<and> aboveS (pred i) \<noteq> {} \<and> succ (pred i) = i"
proof-
  obtain j where a: "aboveS j \<noteq> {}" and i: "i = succ j" using assms unfolding isSucc_def by auto
  have 1: "j \<in> Field r" "j \<noteq> i" unfolding Field_def i
  using succ_diff[OF a] a unfolding aboveS_def by auto
  show ?thesis unfolding pred_def apply(rule someI_ex) using 1 i a by auto
qed

lemmas pred_Field[simp] = pred_Field_succ[THEN conjunct1]
lemmas aboveS_pred[simp] = pred_Field_succ[THEN conjunct2, THEN conjunct1]
lemmas succ_pred[simp] = pred_Field_succ[THEN conjunct2, THEN conjunct2]

lemma isSucc_pred_in:
assumes "isSucc i"  shows "(pred i, i) \<in> r"
proof-
  define j where "j = pred i"
  have i: "i = succ j" using assms unfolding j_def by simp
  have a: "aboveS j \<noteq> {}" unfolding j_def using assms by auto
  show ?thesis unfolding j_def[symmetric] unfolding i using succ_in[OF a] .
qed

lemma isSucc_pred_diff:
assumes "isSucc i"  shows "pred i \<noteq> i"
by (metis aboveS_pred assms succ_diff succ_pred)

(* todo: pred maximal, pred injective? *)

lemma succ_inj[simp]:
assumes "aboveS i \<noteq> {}" and "aboveS j \<noteq> {}"
shows "succ i = succ j \<longleftrightarrow> i = j"
proof safe
  assume s: "succ i = succ j"
  {assume "i \<noteq> j" and "(i,j) \<in> r"
   hence "(succ i, j) \<in> r" using assms by (metis succ_smallest)
   hence False using s assms by (metis succ_not_in)
  }
  moreover
  {assume "i \<noteq> j" and "(j,i) \<in> r"
   hence "(succ j, i) \<in> r" using assms by (metis succ_smallest)
   hence False using s assms by (metis succ_not_in)
  }
  ultimately show "i = j" by (metis TOTALS WELL assms(1) assms(2) succ_in_diff well_order_on_domain)
qed

lemma pred_succ[simp]:
assumes "aboveS j \<noteq> {}"  shows "pred (succ j) = j"
unfolding pred_def apply(rule some_equality)
using assms apply(force simp: Field_def aboveS_def)
by (metis assms succ_inj)

lemma less_succ[simp]:
assumes "aboveS i \<noteq> {}"
shows "(j, succ i) \<in> r \<longleftrightarrow> (j,i) \<in> r \<or> j = succ i"
apply safe
  apply (metis WELL assms in_notinI well_order_on_domain suc_singl_pred succ_def succ_in_diff)
  apply (metis (opaque_lifting, full_types) REFL TRANS assms max2_def max2_equals1 refl_on_domain succ_in_Field succ_not_in transD)
  apply (metis assms in_notinI succ_in_Field)
done

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
"mergeSL S L f i \<equiv>
 if isSucc i then S (pred i) (f (pred i))
 else L f i"


subsubsection \<open>Well-order recursion with (zero), succesor, and limit\<close>

definition worecSL :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where "worecSL S L \<equiv> worec (mergeSL S L)"

definition "adm_woL L \<equiv> \<forall>f g i. isLim i \<and> (\<forall>j\<in>underS i. f j = g j) \<longrightarrow> L f i = L g i"

lemma mergeSL:
assumes "adm_woL L"  shows "adm_wo (mergeSL S L)"
unfolding adm_wo_def proof safe
  fix f g :: "'a => 'b" and i :: 'a
  assume 1: "\<forall>j\<in>underS i. f j = g j"
  show "mergeSL S L f i = mergeSL S L g i"
  proof(cases "isSucc i")
    case True
    hence "pred i \<in> underS i" unfolding underS_def using isSucc_pred_in isSucc_pred_diff by auto
    thus ?thesis using True 1 unfolding mergeSL_def by auto
  next
    case False hence "isLim i" unfolding isLim_def by auto
    thus ?thesis using assms False 1 unfolding mergeSL_def adm_woL_def by auto
  qed
qed

lemma worec_fixpoint1: "adm_wo H \<Longrightarrow> worec H i = H (worec H) i"
by (metis worec_fixpoint)

lemma worecSL_isSucc:
assumes a: "adm_woL L" and i: "isSucc i"
shows "worecSL S L i = S (pred i) (worecSL S L (pred i))"
proof-
  let ?H = "mergeSL S L"
  have "worecSL S L i = ?H (worec ?H) i"
  unfolding worecSL_def using worec_fixpoint1[OF mergeSL[OF a]] .
  also have "... = S (pred i) (worecSL S L (pred i))"
  unfolding worecSL_def mergeSL_def using i by simp
  finally show ?thesis .
qed

lemma worecSL_succ:
assumes a: "adm_woL L" and i: "aboveS j \<noteq> {}"
shows "worecSL S L (succ j) = S j (worecSL S L j)"
proof-
  define i where "i = succ j"
  have i: "isSucc i" by (metis i i_def isSucc_succ)
  have ij: "j = pred i" unfolding i_def using assms by simp
  have 0: "succ (pred i) = i" using i by simp
  show ?thesis unfolding ij using worecSL_isSucc[OF a i] unfolding 0 .
qed

lemma worecSL_isLim:
assumes a: "adm_woL L" and i: "isLim i"
shows "worecSL S L i = L (worecSL S L) i"
proof-
  let ?H = "mergeSL S L"
  have "worecSL S L i = ?H (worec ?H) i"
  unfolding worecSL_def using worec_fixpoint1[OF mergeSL[OF a]] .
  also have "... = L (worecSL S L) i"
  using i unfolding worecSL_def mergeSL_def isLim_def by simp
  finally show ?thesis .
qed

definition worecZSL :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where "worecZSL Z S L \<equiv> worecSL S (\<lambda> f a. if a = zero then Z else L f a)"

lemma worecZSL_zero:
assumes a: "adm_woL L"
shows "worecZSL Z S L zero = Z"
proof-
  let ?L = "\<lambda> f a. if a = zero then Z else L f a"
  have "worecZSL Z S L zero = ?L (worecZSL Z S L) zero"
  unfolding worecZSL_def apply(rule worecSL_isLim)
  using assms unfolding adm_woL_def by auto
  also have "... = Z" by simp
  finally show ?thesis .
qed

lemma worecZSL_succ:
assumes a: "adm_woL L" and i: "aboveS j \<noteq> {}"
shows "worecZSL Z S L (succ j) = S j (worecZSL Z S L j)"
unfolding worecZSL_def apply(rule  worecSL_succ)
using assms unfolding adm_woL_def by auto

lemma worecZSL_isLim:
assumes a: "adm_woL L" and "isLim i" and "i \<noteq> zero"
shows "worecZSL Z S L i = L (worecZSL Z S L) i"
proof-
  let ?L = "\<lambda> f a. if a = zero then Z else L f a"
  have "worecZSL Z S L i = ?L (worecZSL Z S L) i"
  unfolding worecZSL_def apply(rule worecSL_isLim)
  using assms unfolding adm_woL_def by auto
  also have "... = L (worecZSL Z S L) i" using assms by simp
  finally show ?thesis .
qed


subsubsection \<open>Well-order succ-lim induction\<close>

lemma ord_cases:
obtains j where "i = succ j" and "aboveS j \<noteq> {}"  | "isLim i"
by (metis isLim_def isSucc_def)

lemma well_order_inductSL[case_names Suc Lim]:
assumes SUCC: "\<And>i. \<lbrakk>aboveS i \<noteq> {}; P i\<rbrakk> \<Longrightarrow> P (succ i)" and
LIM: "\<And>i. \<lbrakk>isLim i; \<And>j. j \<in> underS i \<Longrightarrow> P j\<rbrakk> \<Longrightarrow> P i"
shows "P i"
proof(induction rule: well_order_induct)
  fix i assume 0:  "\<forall>j. j \<noteq> i \<and> (j, i) \<in> r \<longrightarrow> P j"
  show "P i" proof(cases i rule: ord_cases)
    fix j assume i: "i = succ j" and j: "aboveS j \<noteq> {}"
    hence "j \<noteq> i \<and> (j, i) \<in> r" by (metis  succ_diff succ_in)
    hence 1: "P j" using 0 by simp
    show "P i" unfolding i apply(rule SUCC) using 1 j by auto
  qed(insert 0 LIM, unfold underS_def, auto)
qed

lemma well_order_inductZSL[case_names Zero Suc Lim]:
assumes ZERO: "P zero"
and SUCC: "\<And>i. \<lbrakk>aboveS i \<noteq> {}; P i\<rbrakk> \<Longrightarrow> P (succ i)" and
LIM: "\<And>i. \<lbrakk>isLim i; i \<noteq> zero; \<And>j. j \<in> underS i \<Longrightarrow> P j\<rbrakk> \<Longrightarrow> P i"
shows "P i"
apply(induction rule: well_order_inductSL) using assms by auto

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
unfolding isLimOrd_def isSuccOrd_def proof safe
  fix j assume j: "j \<in> Field r" "\<forall>i\<in>Field r. (i, j) \<in> r"
  hence "(succ j, j) \<in> r" using assms by auto
  moreover have "aboveS j \<noteq> {}" using assms j unfolding aboveS_def by auto
  ultimately show False by (metis succ_not_in)
qed

lemma isLim_iff:
assumes l: "isLim i" and j: "j \<in> underS i"
shows "\<exists> k. k \<in> underS i \<and> j \<in> underS k"
proof-
  have a: "aboveS j \<noteq> {}" using j unfolding underS_def aboveS_def by auto
  show ?thesis apply(rule exI[of _ "succ j"]) apply safe
  using assms a unfolding underS_def isLim_def
  apply (metis (lifting, full_types) isSucc_def mem_Collect_eq succ_smallest)
  by (metis (lifting, full_types) a mem_Collect_eq succ_diff succ_in)
qed

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
     hence "f a \<in> AboveS s (g ` underS r a)" unfolding AboveS_def
     using fa by simp (metis (lifting, full_types) mem_Collect_eq underS_def)
     hence A: "AboveS s (g ` underS r a) \<noteq> {}" by auto
     have B: "\<And> a1. a1 \<in> underS r a \<Longrightarrow> g a1 \<in> underS s (g a)"
     unfolding g apply(rule s.suc_underS[OF A0 A]) by auto
     {fix a1 a2 assume a2: "a2 \<in> underS r a" and 1: "a1 \<in> underS r a2"
      hence a12: "{a1,a2} \<subseteq> under r a2" and "a1 \<noteq> a2" using r.REFL a
      unfolding underS_def under_def refl_on_def Field_def by auto
      hence "g a1 \<noteq> g a2" using IH1a[OF a2] unfolding inj_on_def by auto
      hence "g a1 \<in> underS s (g a2)" using IH1b[OF a2] a12
      unfolding underS_def under_def by auto
     } note C = this
     have ga: "g a \<in> Field s" unfolding g using s.suc_inField[OF A0 A] .
     have aa: "a \<in> under r a"
     using a r.REFL unfolding under_def underS_def refl_on_def by auto
     show ?case proof safe
       show "bij_betw g (under r a) (under s (g a))" unfolding bij_betw_def proof safe
         show "inj_on g (under r a)" proof(rule r.inj_on_Field)
           fix a1 a2 assume "a1 \<in> under r a" and a2: "a2 \<in> under r a" and a1: "a1 \<in> underS r a2"
           hence a22: "a2 \<in> under r a2" and a12: "a1 \<in> under r a2" "a1 \<noteq> a2"
           using a r.REFL unfolding under_def underS_def refl_on_def by auto
           show "g a1 \<noteq> g a2"
           proof(cases "a2 = a")
             case False hence "a2 \<in> underS r a"
             using a2 unfolding underS_def under_def by auto
             from IH1a[OF this] show ?thesis using a12 a22 unfolding inj_on_def by auto
           qed(insert B a1, unfold underS_def, auto)
         qed(unfold under_def Field_def, auto)
       next
         fix a1 assume a1: "a1 \<in> under r a"
         show "g a1 \<in> under s (g a)"
         proof(cases "a1 = a")
           case True thus ?thesis
           using ga s.REFL unfolding refl_on_def under_def by auto
         next
           case False
           hence a1: "a1 \<in> underS r a" using a1 unfolding underS_def under_def by auto
           thus ?thesis using B unfolding underS_def under_def by auto
         qed
       next
         fix b1 assume b1: "b1 \<in> under s (g a)"
         show "b1 \<in> g ` under r a"
         proof(cases "b1 = g a")
           case True thus ?thesis using aa by auto
         next
           case False
           hence "b1 \<in> underS s (g a)" using b1 unfolding underS_def under_def by auto
           from s.underS_suc[OF this[unfolded g] A0]
           obtain a1 where a1: "a1 \<in> underS r a" and b1: "b1 \<in> under s (g a1)" by auto
           obtain a2 where "a2 \<in> under r a1" and b1: "b1 = g a2" using IH1b[OF a1] b1 by auto
           hence "a2 \<in> under r a" using a1
           by (metis r.ANTISYM r.TRANS in_mono underS_subset_under under_underS_trans)
           thus ?thesis using b1 by auto
         qed
       qed
     next
       have "(g a, f a) \<in> s" unfolding g proof(rule s.suc_least[OF A0])
         fix b1 assume "b1 \<in> g ` underS r a"
         then obtain a1 where a1: "b1 = g a1" and a1: "a1 \<in> underS r a" by auto
         hence "b1 \<in> underS s (f a)"
         using a by (metis \<open>\<And>a1. a1 \<in> underS r a \<Longrightarrow> g a1 \<in> underS s (f a)\<close>)
         thus "f a \<noteq> b1 \<and> (b1, f a) \<in> s" unfolding underS_def by auto
       qed(insert fa, auto)
       thus "g a \<in> under s (f a)" unfolding under_def by auto
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
using assms unfolding oproj_def
by (subst (asm) iso_iff3) (auto simp: bij_betw_def)

theorem oproj_embed:
assumes r: "Well_order r" and s: "Well_order s" and f: "oproj r s f"
shows "\<exists> g. embed s r g"
proof (rule embedI[OF s r, of "inv_into (Field r) f"], unfold underS_def, safe)
  fix b assume "b \<in> Field s"
  thus "inv_into (Field r) f b \<in> Field r" using oproj_Field2[OF f] by (metis imageI inv_into_into)
next
  fix a b assume "b \<in> Field s" "a \<noteq> b" "(a, b) \<in> s"
    "inv_into (Field r) f a = inv_into (Field r) f b"
  with f show False by (auto dest!: inv_into_injective simp: Field_def oproj_def)
next
  fix a b assume *: "b \<in> Field s" "a \<noteq> b" "(a, b) \<in> s"
  { assume "(inv_into (Field r) f a, inv_into (Field r) f b) \<notin> r"
    moreover
    from *(3) have "a \<in> Field s" unfolding Field_def by auto
    with *(1,2) have
      "inv_into (Field r) f a \<in> Field r" "inv_into (Field r) f b \<in> Field r"
      "inv_into (Field r) f a \<noteq> inv_into (Field r) f b"
      by (auto dest!: oproj_Field2[OF f] inv_into_injective intro!: inv_into_into)
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
  using oproj_embed[OF assms] r s unfolding ordLeq_def by auto

end
