(*  Title:      HOL/BNF/BNF_LFP.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Least fixed point operation on bounded natural functors.
*)

header {* Least Fixed Point Operation on Bounded Natural Functors *}

theory BNF_LFP
imports BNF_FP
keywords
  "data_raw" :: thy_decl and
  "data" :: thy_decl
begin

lemma subset_emptyI: "(\<And>x. x \<in> A \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> {}"
by blast

lemma image_Collect_subsetI:
  "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> f ` {x. P x} \<subseteq> B"
by blast

lemma Collect_restrict: "{x. x \<in> X \<and> P x} \<subseteq> X"
by auto

lemma prop_restrict: "\<lbrakk>x \<in> Z; Z \<subseteq> {x. x \<in> X \<and> P x}\<rbrakk> \<Longrightarrow> P x"
by auto

lemma underS_I: "\<lbrakk>i \<noteq> j; (i, j) \<in> R\<rbrakk> \<Longrightarrow> i \<in> rel.underS R j"
unfolding rel.underS_def by simp

lemma underS_E: "i \<in> rel.underS R j \<Longrightarrow> i \<noteq> j \<and> (i, j) \<in> R"
unfolding rel.underS_def by simp

lemma underS_Field: "i \<in> rel.underS R j \<Longrightarrow> i \<in> Field R"
unfolding rel.underS_def Field_def by auto

lemma FieldI2: "(i, j) \<in> R \<Longrightarrow> j \<in> Field R"
unfolding Field_def by auto

lemma fst_convol': "fst (<f, g> x) = f x"
using fst_convol unfolding convol_def by simp

lemma snd_convol': "snd (<f, g> x) = g x"
using snd_convol unfolding convol_def by simp

lemma convol_expand_snd: "fst o f = g \<Longrightarrow>  <g, snd o f> = f"
unfolding convol_def by auto

definition inver where
  "inver g f A = (ALL a : A. g (f a) = a)"

lemma bij_betw_iff_ex:
  "bij_betw f A B = (EX g. g ` B = A \<and> inver g f A \<and> inver f g B)" (is "?L = ?R")
proof (rule iffI)
  assume ?L
  hence f: "f ` A = B" and inj_f: "inj_on f A" unfolding bij_betw_def by auto
  let ?phi = "% b a. a : A \<and> f a = b"
  have "ALL b : B. EX a. ?phi b a" using f by blast
  then obtain g where g: "ALL b : B. g b : A \<and> f (g b) = b"
    using bchoice[of B ?phi] by blast
  hence gg: "ALL b : f ` A. g b : A \<and> f (g b) = b" using f by blast
  have gf: "inver g f A" unfolding inver_def
    by (metis (no_types) gg imageI[of _ A f] the_inv_into_f_f[OF inj_f])
  moreover have "g ` B \<le> A \<and> inver f g B" using g unfolding inver_def by blast
  moreover have "A \<le> g ` B"
  proof safe
    fix a assume a: "a : A"
    hence "f a : B" using f by auto
    moreover have "a = g (f a)" using a gf unfolding inver_def by auto
    ultimately show "a : g ` B" by blast
  qed
  ultimately show ?R by blast
next
  assume ?R
  then obtain g where g: "g ` B = A \<and> inver g f A \<and> inver f g B" by blast
  show ?L unfolding bij_betw_def
  proof safe
    show "inj_on f A" unfolding inj_on_def
    proof safe
      fix a1 a2 assume a: "a1 : A"  "a2 : A" and "f a1 = f a2"
      hence "g (f a1) = g (f a2)" by simp
      thus "a1 = a2" using a g unfolding inver_def by simp
    qed
  next
    fix a assume "a : A"
    then obtain b where b: "b : B" and a: "a = g b" using g by blast
    hence "b = f (g b)" using g unfolding inver_def by auto
    thus "f a : B" unfolding a using b by simp
  next
    fix b assume "b : B"
    hence "g b : A \<and> b = f (g b)" using g unfolding inver_def by auto
    thus "b : f ` A" by auto
  qed
qed

lemma bij_betw_ex_weakE:
  "\<lbrakk>bij_betw f A B\<rbrakk> \<Longrightarrow> \<exists>g. g ` B \<subseteq> A \<and> inver g f A \<and> inver f g B"
by (auto simp only: bij_betw_iff_ex)

lemma inver_surj: "\<lbrakk>g ` B \<subseteq> A; f ` A \<subseteq> B; inver g f A\<rbrakk> \<Longrightarrow> g ` B = A"
unfolding inver_def by auto (rule rev_image_eqI, auto)

lemma inver_mono: "\<lbrakk>A \<subseteq> B; inver f g B\<rbrakk> \<Longrightarrow> inver f g A"
unfolding inver_def by auto

lemma inver_pointfree: "inver f g A = (\<forall>a \<in> A. (f o g) a = a)"
unfolding inver_def by simp

lemma bij_betwE: "bij_betw f A B \<Longrightarrow> \<forall>a\<in>A. f a \<in> B"
unfolding bij_betw_def by auto

lemma bij_betw_imageE: "bij_betw f A B \<Longrightarrow> f ` A = B"
unfolding bij_betw_def by auto

lemma inverE: "\<lbrakk>inver f f' A; x \<in> A\<rbrakk> \<Longrightarrow> f (f' x) = x"
unfolding inver_def by auto

lemma bij_betw_inver1: "bij_betw f A B \<Longrightarrow> inver (inv_into A f) f A"
unfolding bij_betw_def inver_def by auto

lemma bij_betw_inver2: "bij_betw f A B \<Longrightarrow> inver f (inv_into A f) B"
unfolding bij_betw_def inver_def by auto

lemma bij_betwI: "\<lbrakk>bij_betw g B A; inver g f A; inver f g B\<rbrakk> \<Longrightarrow> bij_betw f A B"
by (drule bij_betw_imageE, unfold bij_betw_iff_ex) blast

lemma bij_betwI':
  "\<lbrakk>\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (f x = f y) = (x = y);
    \<And>x. x \<in> X \<Longrightarrow> f x \<in> Y;
    \<And>y. y \<in> Y \<Longrightarrow> \<exists>x \<in> X. y = f x\<rbrakk> \<Longrightarrow> bij_betw f X Y"
unfolding bij_betw_def inj_on_def
apply (rule conjI)
 apply blast
by (erule thin_rl) blast

lemma surj_fun_eq:
  assumes surj_on: "f ` X = UNIV" and eq_on: "\<forall>x \<in> X. (g1 o f) x = (g2 o f) x"
  shows "g1 = g2"
proof (rule ext)
  fix y
  from surj_on obtain x where "x \<in> X" and "y = f x" by blast
  thus "g1 y = g2 y" using eq_on by simp
qed

lemma Card_order_wo_rel: "Card_order r \<Longrightarrow> wo_rel r"
unfolding wo_rel_def card_order_on_def by blast

lemma Cinfinite_limit: "\<lbrakk>x \<in> Field r; Cinfinite r\<rbrakk> \<Longrightarrow>
  \<exists>y \<in> Field r. x \<noteq> y \<and> (x, y) \<in> r"
unfolding cinfinite_def by (auto simp add: infinite_Card_order_limit)

lemma Card_order_trans:
  "\<lbrakk>Card_order r; x \<noteq> y; (x, y) \<in> r; y \<noteq> z; (y, z) \<in> r\<rbrakk> \<Longrightarrow> x \<noteq> z \<and> (x, z) \<in> r"
unfolding card_order_on_def well_order_on_def linear_order_on_def
  partial_order_on_def preorder_on_def trans_def antisym_def by blast

lemma Cinfinite_limit2:
 assumes x1: "x1 \<in> Field r" and x2: "x2 \<in> Field r" and r: "Cinfinite r"
 shows "\<exists>y \<in> Field r. (x1 \<noteq> y \<and> (x1, y) \<in> r) \<and> (x2 \<noteq> y \<and> (x2, y) \<in> r)"
proof -
  from r have trans: "trans r" and total: "Total r" and antisym: "antisym r"
    unfolding card_order_on_def well_order_on_def linear_order_on_def
      partial_order_on_def preorder_on_def by auto
  obtain y1 where y1: "y1 \<in> Field r" "x1 \<noteq> y1" "(x1, y1) \<in> r"
    using Cinfinite_limit[OF x1 r] by blast
  obtain y2 where y2: "y2 \<in> Field r" "x2 \<noteq> y2" "(x2, y2) \<in> r"
    using Cinfinite_limit[OF x2 r] by blast
  show ?thesis
  proof (cases "y1 = y2")
    case True with y1 y2 show ?thesis by blast
  next
    case False
    with y1(1) y2(1) total have "(y1, y2) \<in> r \<or> (y2, y1) \<in> r"
      unfolding total_on_def by auto
    thus ?thesis
    proof
      assume *: "(y1, y2) \<in> r"
      with trans y1(3) have "(x1, y2) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x1 = y2") (auto simp: antisym_def)
    next
      assume *: "(y2, y1) \<in> r"
      with trans y2(3) have "(x2, y1) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x2 = y1") (auto simp: antisym_def)
    qed
  qed
qed

lemma Cinfinite_limit_finite: "\<lbrakk>finite X; X \<subseteq> Field r; Cinfinite r\<rbrakk>
 \<Longrightarrow> \<exists>y \<in> Field r. \<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)"
proof (induct X rule: finite_induct)
  case empty thus ?case unfolding cinfinite_def using ex_in_conv[of "Field r"] finite.emptyI by auto
next
  case (insert x X)
  then obtain y where y: "y \<in> Field r" "\<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)" by blast
  then obtain z where z: "z \<in> Field r" "x \<noteq> z \<and> (x, z) \<in> r" "y \<noteq> z \<and> (y, z) \<in> r"
    using Cinfinite_limit2[OF _ y(1) insert(5), of x] insert(4) by blast
  show ?case
    apply (intro bexI ballI)
    apply (erule insertE)
    apply hypsubst
    apply (rule z(2))
    using Card_order_trans[OF insert(5)[THEN conjunct2]] y(2) z(3)
    apply blast
    apply (rule z(1))
    done
qed

lemma insert_subsetI: "\<lbrakk>x \<in> A; X \<subseteq> A\<rbrakk> \<Longrightarrow> insert x X \<subseteq> A"
by auto

(*helps resolution*)
lemma well_order_induct_imp:
  "wo_rel r \<Longrightarrow> (\<And>x. \<forall>y. y \<noteq> x \<and> (y, x) \<in> r \<longrightarrow> y \<in> Field r \<longrightarrow> P y \<Longrightarrow> x \<in> Field r \<longrightarrow> P x) \<Longrightarrow>
     x \<in> Field r \<longrightarrow> P x"
by (erule wo_rel.well_order_induct)

lemma meta_spec2:
  assumes "(\<And>x y. PROP P x y)"
  shows "PROP P x y"
by (rule `(\<And>x y. PROP P x y)`)

ML_file "Tools/bnf_lfp_util.ML"
ML_file "Tools/bnf_lfp_tactics.ML"
ML_file "Tools/bnf_lfp.ML"

end
