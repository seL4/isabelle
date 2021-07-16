(*  Title:      HOL/Conditionally_Complete_Lattices.thy
    Author:     Amine Chaieb and L C Paulson, University of Cambridge
    Author:     Johannes Hölzl, TU München
    Author:     Luke S. Serafin, Carnegie Mellon University
*)

section \<open>Conditionally-complete Lattices\<close>

theory Conditionally_Complete_Lattices
imports Finite_Set Lattices_Big Set_Interval
begin

locale preordering_bdd = preordering
begin

definition bdd :: \<open>'a set \<Rightarrow> bool\<close>
  where unfold: \<open>bdd A \<longleftrightarrow> (\<exists>M. \<forall>x \<in> A. x \<^bold>\<le> M)\<close>

lemma empty [simp, intro]:
  \<open>bdd {}\<close>
  by (simp add: unfold)

lemma I [intro]:
  \<open>bdd A\<close> if \<open>\<And>x. x \<in> A \<Longrightarrow> x \<^bold>\<le> M\<close>
  using that by (auto simp add: unfold)

lemma E:
  assumes \<open>bdd A\<close>
  obtains M where \<open>\<And>x. x \<in> A \<Longrightarrow> x \<^bold>\<le> M\<close>
  using assms that by (auto simp add: unfold)

lemma I2:
  \<open>bdd (f ` A)\<close> if \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<^bold>\<le> M\<close>
  using that by (auto simp add: unfold)

lemma mono:
  \<open>bdd A\<close> if \<open>bdd B\<close> \<open>A \<subseteq> B\<close>
  using that by (auto simp add: unfold)

lemma Int1 [simp]:
  \<open>bdd (A \<inter> B)\<close> if \<open>bdd A\<close>
  using mono that by auto

lemma Int2 [simp]:
  \<open>bdd (A \<inter> B)\<close> if \<open>bdd B\<close>
  using mono that by auto

end

context preorder
begin

sublocale bdd_above: preordering_bdd \<open>(\<le>)\<close> \<open>(<)\<close>
  defines bdd_above_primitive_def: bdd_above = bdd_above.bdd ..

sublocale bdd_below: preordering_bdd \<open>(\<ge>)\<close> \<open>(>)\<close>
  defines bdd_below_primitive_def: bdd_below = bdd_below.bdd ..

lemma bdd_above_def: \<open>bdd_above A \<longleftrightarrow> (\<exists>M. \<forall>x \<in> A. x \<le> M)\<close>
  by (fact bdd_above.unfold)

lemma bdd_below_def: \<open>bdd_below A \<longleftrightarrow> (\<exists>M. \<forall>x \<in> A. M \<le> x)\<close>
  by (fact bdd_below.unfold)

lemma bdd_aboveI: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> M) \<Longrightarrow> bdd_above A"
  by (fact bdd_above.I)

lemma bdd_belowI: "(\<And>x. x \<in> A \<Longrightarrow> m \<le> x) \<Longrightarrow> bdd_below A"
  by (fact bdd_below.I)

lemma bdd_aboveI2: "(\<And>x. x \<in> A \<Longrightarrow> f x \<le> M) \<Longrightarrow> bdd_above (f`A)"
  by (fact bdd_above.I2)

lemma bdd_belowI2: "(\<And>x. x \<in> A \<Longrightarrow> m \<le> f x) \<Longrightarrow> bdd_below (f`A)"
  by (fact bdd_below.I2)

lemma bdd_above_empty: "bdd_above {}"
  by (fact bdd_above.empty)

lemma bdd_below_empty: "bdd_below {}"
  by (fact bdd_below.empty)

lemma bdd_above_mono: "bdd_above B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> bdd_above A"
  by (fact bdd_above.mono)

lemma bdd_below_mono: "bdd_below B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> bdd_below A"
  by (fact bdd_below.mono)

lemma bdd_above_Int1: "bdd_above A \<Longrightarrow> bdd_above (A \<inter> B)"
  by (fact bdd_above.Int1)

lemma bdd_above_Int2: "bdd_above B \<Longrightarrow> bdd_above (A \<inter> B)"
  by (fact bdd_above.Int2)

lemma bdd_below_Int1: "bdd_below A \<Longrightarrow> bdd_below (A \<inter> B)"
  by (fact bdd_below.Int1)

lemma bdd_below_Int2: "bdd_below B \<Longrightarrow> bdd_below (A \<inter> B)"
  by (fact bdd_below.Int2)

lemma bdd_above_Ioo [simp, intro]: "bdd_above {a <..< b}"
  by (auto simp add: bdd_above_def intro!: exI[of _ b] less_imp_le)

lemma bdd_above_Ico [simp, intro]: "bdd_above {a ..< b}"
  by (auto simp add: bdd_above_def intro!: exI[of _ b] less_imp_le)

lemma bdd_above_Iio [simp, intro]: "bdd_above {..< b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Ioc [simp, intro]: "bdd_above {a <.. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Icc [simp, intro]: "bdd_above {a .. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_above_Iic [simp, intro]: "bdd_above {.. b}"
  by (auto simp add: bdd_above_def intro: exI[of _ b] less_imp_le)

lemma bdd_below_Ioo [simp, intro]: "bdd_below {a <..< b}"
  by (auto simp add: bdd_below_def intro!: exI[of _ a] less_imp_le)

lemma bdd_below_Ioc [simp, intro]: "bdd_below {a <.. b}"
  by (auto simp add: bdd_below_def intro!: exI[of _ a] less_imp_le)

lemma bdd_below_Ioi [simp, intro]: "bdd_below {a <..}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Ico [simp, intro]: "bdd_below {a ..< b}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Icc [simp, intro]: "bdd_below {a .. b}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

lemma bdd_below_Ici [simp, intro]: "bdd_below {a ..}"
  by (auto simp add: bdd_below_def intro: exI[of _ a] less_imp_le)

end

context order_top
begin

lemma bdd_above_top [simp, intro!]: "bdd_above A"
  by (rule bdd_aboveI [of _ top]) simp

end

context order_bot
begin

lemma bdd_below_bot [simp, intro!]: "bdd_below A"
  by (rule bdd_belowI [of _ bot]) simp

end

lemma bdd_above_image_mono: "mono f \<Longrightarrow> bdd_above A \<Longrightarrow> bdd_above (f`A)"
  by (auto simp: bdd_above_def mono_def)

lemma bdd_below_image_mono: "mono f \<Longrightarrow> bdd_below A \<Longrightarrow> bdd_below (f`A)"
  by (auto simp: bdd_below_def mono_def)

lemma bdd_above_image_antimono: "antimono f \<Longrightarrow> bdd_below A \<Longrightarrow> bdd_above (f`A)"
  by (auto simp: bdd_above_def bdd_below_def antimono_def)

lemma bdd_below_image_antimono: "antimono f \<Longrightarrow> bdd_above A \<Longrightarrow> bdd_below (f`A)"
  by (auto simp: bdd_above_def bdd_below_def antimono_def)

lemma
  fixes X :: "'a::ordered_ab_group_add set"
  shows bdd_above_uminus[simp]: "bdd_above (uminus ` X) \<longleftrightarrow> bdd_below X"
    and bdd_below_uminus[simp]: "bdd_below (uminus ` X) \<longleftrightarrow> bdd_above X"
  using bdd_above_image_antimono[of uminus X] bdd_below_image_antimono[of uminus "uminus`X"]
  using bdd_below_image_antimono[of uminus X] bdd_above_image_antimono[of uminus "uminus`X"]
  by (auto simp: antimono_def image_image)

context lattice
begin

lemma bdd_above_insert [simp]: "bdd_above (insert a A) = bdd_above A"
  by (auto simp: bdd_above_def intro: le_supI2 sup_ge1)

lemma bdd_below_insert [simp]: "bdd_below (insert a A) = bdd_below A"
  by (auto simp: bdd_below_def intro: le_infI2 inf_le1)

lemma bdd_finite [simp]:
  assumes "finite A" shows bdd_above_finite: "bdd_above A" and bdd_below_finite: "bdd_below A"
  using assms by (induct rule: finite_induct, auto)

lemma bdd_above_Un [simp]: "bdd_above (A \<union> B) = (bdd_above A \<and> bdd_above B)"
proof
  assume "bdd_above (A \<union> B)"
  thus "bdd_above A \<and> bdd_above B" unfolding bdd_above_def by auto
next
  assume "bdd_above A \<and> bdd_above B"
  then obtain a b where "\<forall>x\<in>A. x \<le> a" "\<forall>x\<in>B. x \<le> b" unfolding bdd_above_def by auto
  hence "\<forall>x \<in> A \<union> B. x \<le> sup a b" by (auto intro: Un_iff le_supI1 le_supI2)
  thus "bdd_above (A \<union> B)" unfolding bdd_above_def ..
qed

lemma bdd_below_Un [simp]: "bdd_below (A \<union> B) = (bdd_below A \<and> bdd_below B)"
proof
  assume "bdd_below (A \<union> B)"
  thus "bdd_below A \<and> bdd_below B" unfolding bdd_below_def by auto
next
  assume "bdd_below A \<and> bdd_below B"
  then obtain a b where "\<forall>x\<in>A. a \<le> x" "\<forall>x\<in>B. b \<le> x" unfolding bdd_below_def by auto
  hence "\<forall>x \<in> A \<union> B. inf a b \<le> x" by (auto intro: Un_iff le_infI1 le_infI2)
  thus "bdd_below (A \<union> B)" unfolding bdd_below_def ..
qed

lemma bdd_above_image_sup[simp]:
  "bdd_above ((\<lambda>x. sup (f x) (g x)) ` A) \<longleftrightarrow> bdd_above (f`A) \<and> bdd_above (g`A)"
by (auto simp: bdd_above_def intro: le_supI1 le_supI2)

lemma bdd_below_image_inf[simp]:
  "bdd_below ((\<lambda>x. inf (f x) (g x)) ` A) \<longleftrightarrow> bdd_below (f`A) \<and> bdd_below (g`A)"
by (auto simp: bdd_below_def intro: le_infI1 le_infI2)

lemma bdd_below_UN[simp]: "finite I \<Longrightarrow> bdd_below (\<Union>i\<in>I. A i) = (\<forall>i \<in> I. bdd_below (A i))"
by (induction I rule: finite.induct) auto

lemma bdd_above_UN[simp]: "finite I \<Longrightarrow> bdd_above (\<Union>i\<in>I. A i) = (\<forall>i \<in> I. bdd_above (A i))"
by (induction I rule: finite.induct) auto

end


text \<open>

To avoid name classes with the \<^class>\<open>complete_lattice\<close>-class we prefix \<^const>\<open>Sup\<close> and
\<^const>\<open>Inf\<close> in theorem names with c.

\<close>

class conditionally_complete_lattice = lattice + Sup + Inf +
  assumes cInf_lower: "x \<in> X \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X \<le> x"
    and cInf_greatest: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf X"
  assumes cSup_upper: "x \<in> X \<Longrightarrow> bdd_above X \<Longrightarrow> x \<le> Sup X"
    and cSup_least: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
begin

lemma cSup_upper2: "x \<in> X \<Longrightarrow> y \<le> x \<Longrightarrow> bdd_above X \<Longrightarrow> y \<le> Sup X"
  by (metis cSup_upper order_trans)

lemma cInf_lower2: "x \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X \<le> y"
  by (metis cInf_lower order_trans)

lemma cSup_mono: "B \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. b \<le> a) \<Longrightarrow> Sup B \<le> Sup A"
  by (metis cSup_least cSup_upper2)

lemma cInf_mono: "B \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b) \<Longrightarrow> Inf A \<le> Inf B"
  by (metis cInf_greatest cInf_lower2)

lemma cSup_subset_mono: "A \<noteq> {} \<Longrightarrow> bdd_above B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A \<le> Sup B"
  by (metis cSup_least cSup_upper subsetD)

lemma cInf_superset_mono: "A \<noteq> {} \<Longrightarrow> bdd_below B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inf B \<le> Inf A"
  by (metis cInf_greatest cInf_lower subsetD)

lemma cSup_eq_maximum: "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X = z"
  by (intro order.antisym cSup_upper[of z X] cSup_least[of X z]) auto

lemma cInf_eq_minimum: "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X = z"
  by (intro order.antisym cInf_lower[of z X] cInf_greatest[of X z]) auto

lemma cSup_le_iff: "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> Sup S \<le> a \<longleftrightarrow> (\<forall>x\<in>S. x \<le> a)"
  by (metis order_trans cSup_upper cSup_least)

lemma le_cInf_iff: "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> a \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. a \<le> x)"
  by (metis order_trans cInf_lower cInf_greatest)

lemma cSup_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> x \<le> a"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y"
  shows "Sup X = a"
  by (intro 3 1 order.antisym cSup_least) (auto intro: 2 1 cSup_upper)

lemma cInf_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> a \<le> x"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a"
  shows "Inf X = a"
  by (intro 3 1 order.antisym cInf_greatest) (auto intro: 2 1 cInf_lower)

lemma cInf_cSup: "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> Inf S = Sup {x. \<forall>s\<in>S. x \<le> s}"
  by (rule cInf_eq_non_empty) (auto intro!: cSup_upper cSup_least simp: bdd_below_def)

lemma cSup_cInf: "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> Sup S = Inf {x. \<forall>s\<in>S. s \<le> x}"
  by (rule cSup_eq_non_empty) (auto intro!: cInf_lower cInf_greatest simp: bdd_above_def)

lemma cSup_insert: "X \<noteq> {} \<Longrightarrow> bdd_above X \<Longrightarrow> Sup (insert a X) = sup a (Sup X)"
  by (intro cSup_eq_non_empty) (auto intro: le_supI2 cSup_upper cSup_least)

lemma cInf_insert: "X \<noteq> {} \<Longrightarrow> bdd_below X \<Longrightarrow> Inf (insert a X) = inf a (Inf X)"
  by (intro cInf_eq_non_empty) (auto intro: le_infI2 cInf_lower cInf_greatest)

lemma cSup_singleton [simp]: "Sup {x} = x"
  by (intro cSup_eq_maximum) auto

lemma cInf_singleton [simp]: "Inf {x} = x"
  by (intro cInf_eq_minimum) auto

lemma cSup_insert_If:  "bdd_above X \<Longrightarrow> Sup (insert a X) = (if X = {} then a else sup a (Sup X))"
  using cSup_insert[of X] by simp

lemma cInf_insert_If: "bdd_below X \<Longrightarrow> Inf (insert a X) = (if X = {} then a else inf a (Inf X))"
  using cInf_insert[of X] by simp

lemma le_cSup_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> Sup X"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    by (cases "X = {}") (auto simp: cSup_insert intro: le_supI2)
qed simp

lemma cInf_le_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf X \<le> x"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    by (cases "X = {}") (auto simp: cInf_insert intro: le_infI2)
qed simp

lemma cSup_eq_Sup_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Sup_fin X"
  by (induct X rule: finite_ne_induct) (simp_all add: cSup_insert)

lemma cInf_eq_Inf_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Inf_fin X"
  by (induct X rule: finite_ne_induct) (simp_all add: cInf_insert)

lemma cSup_atMost[simp]: "Sup {..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cSup_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Sup {y<..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cSup_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Sup {y..x} = x"
  by (auto intro!: cSup_eq_maximum)

lemma cInf_atLeast[simp]: "Inf {x..} = x"
  by (auto intro!: cInf_eq_minimum)

lemma cInf_atLeastLessThan[simp]: "y < x \<Longrightarrow> Inf {y..<x} = y"
  by (auto intro!: cInf_eq_minimum)

lemma cInf_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Inf {y..x} = y"
  by (auto intro!: cInf_eq_minimum)

lemma cINF_lower: "bdd_below (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> \<Sqinter>(f ` A) \<le> f x"
  using cInf_lower [of _ "f ` A"] by simp

lemma cINF_greatest: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> m \<le> f x) \<Longrightarrow> m \<le> \<Sqinter>(f ` A)"
  using cInf_greatest [of "f ` A"] by auto

lemma cSUP_upper: "x \<in> A \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> f x \<le> \<Squnion>(f ` A)"
  using cSup_upper [of _ "f ` A"] by simp

lemma cSUP_least: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<le> M) \<Longrightarrow> \<Squnion>(f ` A) \<le> M"
  using cSup_least [of "f ` A"] by auto

lemma cINF_lower2: "bdd_below (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<le> u \<Longrightarrow> \<Sqinter>(f ` A) \<le> u"
  by (auto intro: cINF_lower order_trans)

lemma cSUP_upper2: "bdd_above (f ` A) \<Longrightarrow> x \<in> A \<Longrightarrow> u \<le> f x \<Longrightarrow> u \<le> \<Squnion>(f ` A)"
  by (auto intro: cSUP_upper order_trans)

lemma cSUP_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion>x\<in>A. c) = c"
  by (intro order.antisym cSUP_least) (auto intro: cSUP_upper)

lemma cINF_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter>x\<in>A. c) = c"
  by (intro order.antisym cINF_greatest) (auto intro: cINF_lower)

lemma le_cINF_iff: "A \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> u \<le> \<Sqinter>(f ` A) \<longleftrightarrow> (\<forall>x\<in>A. u \<le> f x)"
  by (metis cINF_greatest cINF_lower order_trans)

lemma cSUP_le_iff: "A \<noteq> {} \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> \<Squnion>(f ` A) \<le> u \<longleftrightarrow> (\<forall>x\<in>A. f x \<le> u)"
  by (metis cSUP_least cSUP_upper order_trans)

lemma less_cINF_D: "bdd_below (f`A) \<Longrightarrow> y < (\<Sqinter>i\<in>A. f i) \<Longrightarrow> i \<in> A \<Longrightarrow> y < f i"
  by (metis cINF_lower less_le_trans)

lemma cSUP_lessD: "bdd_above (f`A) \<Longrightarrow> (\<Squnion>i\<in>A. f i) < y \<Longrightarrow> i \<in> A \<Longrightarrow> f i < y"
  by (metis cSUP_upper le_less_trans)

lemma cINF_insert: "A \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> \<Sqinter>(f ` insert a A) = inf (f a) (\<Sqinter>(f ` A))"
  by (simp add: cInf_insert)

lemma cSUP_insert: "A \<noteq> {} \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> \<Squnion>(f ` insert a A) = sup (f a) (\<Squnion>(f ` A))"
  by (simp add: cSup_insert)

lemma cINF_mono: "B \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> (\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> \<Sqinter>(f ` A) \<le> \<Sqinter>(g ` B)"
  using cInf_mono [of "g ` B" "f ` A"] by auto

lemma cSUP_mono: "A \<noteq> {} \<Longrightarrow> bdd_above (g ` B) \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le> g m) \<Longrightarrow> \<Squnion>(f ` A) \<le> \<Squnion>(g ` B)"
  using cSup_mono [of "f ` A" "g ` B"] by auto

lemma cINF_superset_mono: "A \<noteq> {} \<Longrightarrow> bdd_below (g ` B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> g x \<le> f x) \<Longrightarrow> \<Sqinter>(g ` B) \<le> \<Sqinter>(f ` A)"
  by (rule cINF_mono) auto

lemma cSUP_subset_mono: 
  "\<lbrakk>A \<noteq> {}; bdd_above (g ` B); A \<subseteq> B; \<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<rbrakk> \<Longrightarrow> \<Squnion> (f ` A) \<le> \<Squnion> (g ` B)"
  by (rule cSUP_mono) auto

lemma less_eq_cInf_inter: "bdd_below A \<Longrightarrow> bdd_below B \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> inf (Inf A) (Inf B) \<le> Inf (A \<inter> B)"
  by (metis cInf_superset_mono lattice_class.inf_sup_ord(1) le_infI1)

lemma cSup_inter_less_eq: "bdd_above A \<Longrightarrow> bdd_above B \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> Sup (A \<inter> B) \<le> sup (Sup A) (Sup B) "
  by (metis cSup_subset_mono lattice_class.inf_sup_ord(1) le_supI1)

lemma cInf_union_distrib: "A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_below B \<Longrightarrow> Inf (A \<union> B) = inf (Inf A) (Inf B)"
  by (intro order.antisym le_infI cInf_greatest cInf_lower) (auto intro: le_infI1 le_infI2 cInf_lower)

lemma cINF_union: "A \<noteq> {} \<Longrightarrow> bdd_below (f ` A) \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_below (f ` B) \<Longrightarrow> \<Sqinter> (f ` (A \<union> B)) = \<Sqinter> (f ` A) \<sqinter> \<Sqinter> (f ` B)"
  using cInf_union_distrib [of "f ` A" "f ` B"] by (simp add: image_Un)

lemma cSup_union_distrib: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_above B \<Longrightarrow> Sup (A \<union> B) = sup (Sup A) (Sup B)"
  by (intro order.antisym le_supI cSup_least cSup_upper) (auto intro: le_supI1 le_supI2 cSup_upper)

lemma cSUP_union: "A \<noteq> {} \<Longrightarrow> bdd_above (f ` A) \<Longrightarrow> B \<noteq> {} \<Longrightarrow> bdd_above (f ` B) \<Longrightarrow> \<Squnion> (f ` (A \<union> B)) = \<Squnion> (f ` A) \<squnion> \<Squnion> (f ` B)"
  using cSup_union_distrib [of "f ` A" "f ` B"] by (simp add: image_Un)

lemma cINF_inf_distrib: "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> bdd_below (g`A) \<Longrightarrow> \<Sqinter> (f ` A) \<sqinter> \<Sqinter> (g ` A) = (\<Sqinter>a\<in>A. inf (f a) (g a))"
  by (intro order.antisym le_infI cINF_greatest cINF_lower2)
     (auto intro: le_infI1 le_infI2 cINF_greatest cINF_lower le_infI)

lemma SUP_sup_distrib: "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> bdd_above (g`A) \<Longrightarrow> \<Squnion> (f ` A) \<squnion> \<Squnion> (g ` A) = (\<Squnion>a\<in>A. sup (f a) (g a))"
  by (intro order.antisym le_supI cSUP_least cSUP_upper2)
     (auto intro: le_supI1 le_supI2 cSUP_least cSUP_upper le_supI)

lemma cInf_le_cSup:
  "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<le> Sup A"
  by (auto intro!: cSup_upper2[of "SOME a. a \<in> A"] intro: someI cInf_lower)

  context
    fixes f :: "'a \<Rightarrow> 'b::conditionally_complete_lattice"
    assumes "mono f"
  begin
  
  lemma mono_cInf: "\<lbrakk>bdd_below A; A\<noteq>{}\<rbrakk> \<Longrightarrow> f (Inf A) \<le> (INF x\<in>A. f x)"
    by (simp add: \<open>mono f\<close> conditionally_complete_lattice_class.cINF_greatest cInf_lower monoD)
  
  lemma mono_cSup: "\<lbrakk>bdd_above A; A\<noteq>{}\<rbrakk> \<Longrightarrow> (SUP x\<in>A. f x) \<le> f (Sup A)"
    by (simp add: \<open>mono f\<close> conditionally_complete_lattice_class.cSUP_least cSup_upper monoD)
  
  lemma mono_cINF: "\<lbrakk>bdd_below (A`I); I\<noteq>{}\<rbrakk> \<Longrightarrow> f (INF i\<in>I. A i) \<le> (INF x\<in>I. f (A x))"
    by (simp add: \<open>mono f\<close> conditionally_complete_lattice_class.cINF_greatest cINF_lower monoD)
  
  lemma mono_cSUP: "\<lbrakk>bdd_above (A`I); I\<noteq>{}\<rbrakk> \<Longrightarrow> (SUP x\<in>I. f (A x)) \<le> f (SUP i\<in>I. A i)"
    by (simp add: \<open>mono f\<close> conditionally_complete_lattice_class.cSUP_least cSUP_upper monoD)
  
  end

end

instance complete_lattice \<subseteq> conditionally_complete_lattice
  by standard (auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)

lemma cSup_eq:
  fixes a :: "'a :: {conditionally_complete_lattice, no_bot}"
  assumes upper: "\<And>x. x \<in> X \<Longrightarrow> x \<le> a"
  assumes least: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y"
  shows "Sup X = a"
proof cases
  assume "X = {}" with lt_ex[of a] least show ?thesis by (auto simp: less_le_not_le)
qed (intro cSup_eq_non_empty assms)

lemma cInf_eq:
  fixes a :: "'a :: {conditionally_complete_lattice, no_top}"
  assumes upper: "\<And>x. x \<in> X \<Longrightarrow> a \<le> x"
  assumes least: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a"
  shows "Inf X = a"
proof cases
  assume "X = {}" with gt_ex[of a] least show ?thesis by (auto simp: less_le_not_le)
qed (intro cInf_eq_non_empty assms)

class conditionally_complete_linorder = conditionally_complete_lattice + linorder
begin

lemma less_cSup_iff:
  "X \<noteq> {} \<Longrightarrow> bdd_above X \<Longrightarrow> y < Sup X \<longleftrightarrow> (\<exists>x\<in>X. y < x)"
  by (rule iffI) (metis cSup_least not_less, metis cSup_upper less_le_trans)

lemma cInf_less_iff: "X \<noteq> {} \<Longrightarrow> bdd_below X \<Longrightarrow> Inf X < y \<longleftrightarrow> (\<exists>x\<in>X. x < y)"
  by (rule iffI) (metis cInf_greatest not_less, metis cInf_lower le_less_trans)

lemma cINF_less_iff: "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> (\<Sqinter>i\<in>A. f i) < a \<longleftrightarrow> (\<exists>x\<in>A. f x < a)"
  using cInf_less_iff[of "f`A"] by auto

lemma less_cSUP_iff: "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> a < (\<Squnion>i\<in>A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a < f x)"
  using less_cSup_iff[of "f`A"] by auto

lemma less_cSupE:
  assumes "y < Sup X" "X \<noteq> {}" obtains x where "x \<in> X" "y < x"
  by (metis cSup_least assms not_le that)

lemma less_cSupD:
  "X \<noteq> {} \<Longrightarrow> z < Sup X \<Longrightarrow> \<exists>x\<in>X. z < x"
  by (metis less_cSup_iff not_le_imp_less bdd_above_def)

lemma cInf_lessD:
  "X \<noteq> {} \<Longrightarrow> Inf X < z \<Longrightarrow> \<exists>x\<in>X. x < z"
  by (metis cInf_less_iff not_le_imp_less bdd_below_def)

lemma complete_interval:
  assumes "a < b" and "P a" and "\<not> P b"
  shows "\<exists>c. a \<le> c \<and> c \<le> b \<and> (\<forall>x. a \<le> x \<and> x < c \<longrightarrow> P x) \<and>
             (\<forall>d. (\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x) \<longrightarrow> d \<le> c)"
proof (rule exI [where x = "Sup {d. \<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x}"], auto)
  show "a \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
    by (rule cSup_upper, auto simp: bdd_above_def)
       (metis \<open>a < b\<close> \<open>\<not> P b\<close> linear less_le)
next
  show "Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c} \<le> b"
    apply (rule cSup_least)
    apply auto
    apply (metis less_le_not_le)
    apply (metis \<open>a<b\<close> \<open>\<not> P b\<close> linear less_le)
    done
next
  fix x
  assume x: "a \<le> x" and lt: "x < Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
  show "P x"
    apply (rule less_cSupE [OF lt], auto)
    apply (metis less_le_not_le)
    apply (metis x)
    done
next
  fix d
    assume 0: "\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x"
    thus "d \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
      by (rule_tac cSup_upper, auto simp: bdd_above_def)
         (metis \<open>a<b\<close> \<open>\<not> P b\<close> linear less_le)
qed

end

instance complete_linorder < conditionally_complete_linorder
  ..

lemma cSup_eq_Max: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Max X"
  using cSup_eq_Sup_fin[of X] by (simp add: Sup_fin_Max)

lemma cInf_eq_Min: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Min X"
  using cInf_eq_Inf_fin[of X] by (simp add: Inf_fin_Min)

lemma cSup_lessThan[simp]: "Sup {..<x::'a::{conditionally_complete_linorder, no_bot, dense_linorder}} = x"
  by (auto intro!: cSup_eq_non_empty intro: dense_le)

lemma cSup_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Sup {y<..<x::'a::{conditionally_complete_linorder, dense_linorder}} = x"
  by (auto intro!: cSup_eq_non_empty intro: dense_le_bounded)

lemma cSup_atLeastLessThan[simp]: "y < x \<Longrightarrow> Sup {y..<x::'a::{conditionally_complete_linorder, dense_linorder}} = x"
  by (auto intro!: cSup_eq_non_empty intro: dense_le_bounded)

lemma cInf_greaterThan[simp]: "Inf {x::'a::{conditionally_complete_linorder, no_top, dense_linorder} <..} = x"
  by (auto intro!: cInf_eq_non_empty intro: dense_ge)

lemma cInf_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Inf {y<..x::'a::{conditionally_complete_linorder, dense_linorder}} = y"
  by (auto intro!: cInf_eq_non_empty intro: dense_ge_bounded)

lemma cInf_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Inf {y<..<x::'a::{conditionally_complete_linorder, dense_linorder}} = y"
  by (auto intro!: cInf_eq_non_empty intro: dense_ge_bounded)

lemma Inf_insert_finite:
  fixes S :: "'a::conditionally_complete_linorder set"
  shows "finite S \<Longrightarrow> Inf (insert x S) = (if S = {} then x else min x (Inf S))"
  by (simp add: cInf_eq_Min)

lemma Sup_insert_finite:
  fixes S :: "'a::conditionally_complete_linorder set"
  shows "finite S \<Longrightarrow> Sup (insert x S) = (if S = {} then x else max x (Sup S))"
  by (simp add: cSup_insert sup_max)

lemma finite_imp_less_Inf:
  fixes a :: "'a::conditionally_complete_linorder"
  shows "\<lbrakk>finite X; x \<in> X; \<And>x. x\<in>X \<Longrightarrow> a < x\<rbrakk> \<Longrightarrow> a < Inf X"
  by (induction X rule: finite_induct) (simp_all add: cInf_eq_Min Inf_insert_finite)

lemma finite_less_Inf_iff:
  fixes a :: "'a :: conditionally_complete_linorder"
  shows "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> a < Inf X \<longleftrightarrow> (\<forall>x \<in> X. a < x)"
  by (auto simp: cInf_eq_Min)

lemma finite_imp_Sup_less:
  fixes a :: "'a::conditionally_complete_linorder"
  shows "\<lbrakk>finite X; x \<in> X; \<And>x. x\<in>X \<Longrightarrow> a > x\<rbrakk> \<Longrightarrow> a > Sup X"
  by (induction X rule: finite_induct) (simp_all add: cSup_eq_Max Sup_insert_finite)

lemma finite_Sup_less_iff:
  fixes a :: "'a :: conditionally_complete_linorder"
  shows "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> a > Sup X \<longleftrightarrow> (\<forall>x \<in> X. a > x)"
  by (auto simp: cSup_eq_Max)

class linear_continuum = conditionally_complete_linorder + dense_linorder +
  assumes UNIV_not_singleton: "\<exists>a b::'a. a \<noteq> b"
begin

lemma ex_gt_or_lt: "\<exists>b. a < b \<or> b < a"
  by (metis UNIV_not_singleton neq_iff)

end

instantiation nat :: conditionally_complete_linorder
begin

definition "Sup (X::nat set) = (if X={} then 0 else Max X)"
definition "Inf (X::nat set) = (LEAST n. n \<in> X)"

lemma bdd_above_nat: "bdd_above X \<longleftrightarrow> finite (X::nat set)"
proof
  assume "bdd_above X"
  then obtain z where "X \<subseteq> {.. z}"
    by (auto simp: bdd_above_def)
  then show "finite X"
    by (rule finite_subset) simp
qed simp

instance
proof
  fix x :: nat
  fix X :: "nat set"
  show "Inf X \<le> x" if "x \<in> X" "bdd_below X"
    using that by (simp add: Inf_nat_def Least_le)
  show "x \<le> Inf X" if "X \<noteq> {}" "\<And>y. y \<in> X \<Longrightarrow> x \<le> y"
    using that unfolding Inf_nat_def ex_in_conv[symmetric] by (rule LeastI2_ex)
  show "x \<le> Sup X" if "x \<in> X" "bdd_above X"
    using that by (auto simp add: Sup_nat_def bdd_above_nat)
  show "Sup X \<le> x" if "X \<noteq> {}" "\<And>y. y \<in> X \<Longrightarrow> y \<le> x"
  proof -
    from that have "bdd_above X"
      by (auto simp: bdd_above_def)
    with that show ?thesis 
      by (simp add: Sup_nat_def bdd_above_nat)
  qed
qed

end

lemma Inf_nat_def1:
  fixes K::"nat set"
  assumes "K \<noteq> {}"
  shows "Inf K \<in> K"
by (auto simp add: Min_def Inf_nat_def) (meson LeastI assms bot.extremum_unique subsetI)

lemma Sup_nat_empty [simp]: "Sup {} = (0::nat)"
  by (auto simp add: Sup_nat_def) 



instantiation int :: conditionally_complete_linorder
begin

definition "Sup (X::int set) = (THE x. x \<in> X \<and> (\<forall>y\<in>X. y \<le> x))"
definition "Inf (X::int set) = - (Sup (uminus ` X))"

instance
proof
  { fix x :: int and X :: "int set" assume "X \<noteq> {}" "bdd_above X"
    then obtain x y where "X \<subseteq> {..y}" "x \<in> X"
      by (auto simp: bdd_above_def)
    then have *: "finite (X \<inter> {x..y})" "X \<inter> {x..y} \<noteq> {}" and "x \<le> y"
      by (auto simp: subset_eq)
    have "\<exists>!x\<in>X. (\<forall>y\<in>X. y \<le> x)"
    proof
      { fix z assume "z \<in> X"
        have "z \<le> Max (X \<inter> {x..y})"
        proof cases
          assume "x \<le> z" with \<open>z \<in> X\<close> \<open>X \<subseteq> {..y}\<close> *(1) show ?thesis
            by (auto intro!: Max_ge)
        next
          assume "\<not> x \<le> z"
          then have "z < x" by simp
          also have "x \<le> Max (X \<inter> {x..y})"
            using \<open>x \<in> X\<close> *(1) \<open>x \<le> y\<close> by (intro Max_ge) auto
          finally show ?thesis by simp
        qed }
      note le = this
      with Max_in[OF *] show ex: "Max (X \<inter> {x..y}) \<in> X \<and> (\<forall>z\<in>X. z \<le> Max (X \<inter> {x..y}))" by auto

      fix z assume *: "z \<in> X \<and> (\<forall>y\<in>X. y \<le> z)"
      with le have "z \<le> Max (X \<inter> {x..y})"
        by auto
      moreover have "Max (X \<inter> {x..y}) \<le> z"
        using * ex by auto
      ultimately show "z = Max (X \<inter> {x..y})"
        by auto
    qed
    then have "Sup X \<in> X \<and> (\<forall>y\<in>X. y \<le> Sup X)"
      unfolding Sup_int_def by (rule theI') }
  note Sup_int = this

  { fix x :: int and X :: "int set" assume "x \<in> X" "bdd_above X" then show "x \<le> Sup X"
      using Sup_int[of X] by auto }
  note le_Sup = this
  { fix x :: int and X :: "int set" assume "X \<noteq> {}" "\<And>y. y \<in> X \<Longrightarrow> y \<le> x" then show "Sup X \<le> x"
      using Sup_int[of X] by (auto simp: bdd_above_def) }
  note Sup_le = this

  { fix x :: int and X :: "int set" assume "x \<in> X" "bdd_below X" then show "Inf X \<le> x"
      using le_Sup[of "-x" "uminus ` X"] by (auto simp: Inf_int_def) }
  { fix x :: int and X :: "int set" assume "X \<noteq> {}" "\<And>y. y \<in> X \<Longrightarrow> x \<le> y" then show "x \<le> Inf X"
      using Sup_le[of "uminus ` X" "-x"] by (force simp: Inf_int_def) }
qed
end

lemma interval_cases:
  fixes S :: "'a :: conditionally_complete_linorder set"
  assumes ivl: "\<And>a b x. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<in> S"
  shows "\<exists>a b. S = {} \<or>
    S = UNIV \<or>
    S = {..<b} \<or>
    S = {..b} \<or>
    S = {a<..} \<or>
    S = {a..} \<or>
    S = {a<..<b} \<or>
    S = {a<..b} \<or>
    S = {a..<b} \<or>
    S = {a..b}"
proof -
  define lower upper where "lower = {x. \<exists>s\<in>S. s \<le> x}" and "upper = {x. \<exists>s\<in>S. x \<le> s}"
  with ivl have "S = lower \<inter> upper"
    by auto
  moreover
  have "\<exists>a. upper = UNIV \<or> upper = {} \<or> upper = {.. a} \<or> upper = {..< a}"
  proof cases
    assume *: "bdd_above S \<and> S \<noteq> {}"
    from * have "upper \<subseteq> {.. Sup S}"
      by (auto simp: upper_def intro: cSup_upper2)
    moreover from * have "{..< Sup S} \<subseteq> upper"
      by (force simp add: less_cSup_iff upper_def subset_eq Ball_def)
    ultimately have "upper = {.. Sup S} \<or> upper = {..< Sup S}"
      unfolding ivl_disj_un(2)[symmetric] by auto
    then show ?thesis by auto
  next
    assume "\<not> (bdd_above S \<and> S \<noteq> {})"
    then have "upper = UNIV \<or> upper = {}"
      by (auto simp: upper_def bdd_above_def not_le dest: less_imp_le)
    then show ?thesis
      by auto
  qed
  moreover
  have "\<exists>b. lower = UNIV \<or> lower = {} \<or> lower = {b ..} \<or> lower = {b <..}"
  proof cases
    assume *: "bdd_below S \<and> S \<noteq> {}"
    from * have "lower \<subseteq> {Inf S ..}"
      by (auto simp: lower_def intro: cInf_lower2)
    moreover from * have "{Inf S <..} \<subseteq> lower"
      by (force simp add: cInf_less_iff lower_def subset_eq Ball_def)
    ultimately have "lower = {Inf S ..} \<or> lower = {Inf S <..}"
      unfolding ivl_disj_un(1)[symmetric] by auto
    then show ?thesis by auto
  next
    assume "\<not> (bdd_below S \<and> S \<noteq> {})"
    then have "lower = UNIV \<or> lower = {}"
      by (auto simp: lower_def bdd_below_def not_le dest: less_imp_le)
    then show ?thesis
      by auto
  qed
  ultimately show ?thesis
    unfolding greaterThanAtMost_def greaterThanLessThan_def atLeastAtMost_def atLeastLessThan_def
    by (metis inf_bot_left inf_bot_right inf_top.left_neutral inf_top.right_neutral)
qed

lemma cSUP_eq_cINF_D:
  fixes f :: "_ \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes eq: "(\<Squnion>x\<in>A. f x) = (\<Sqinter>x\<in>A. f x)"
     and bdd: "bdd_above (f ` A)" "bdd_below (f ` A)"
     and a: "a \<in> A"
  shows "f a = (\<Sqinter>x\<in>A. f x)"
apply (rule antisym)
using a bdd
apply (auto simp: cINF_lower)
apply (metis eq cSUP_upper)
done

lemma cSUP_UNION:
  fixes f :: "_ \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes ne: "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> B(x) \<noteq> {}"
      and bdd_UN: "bdd_above (\<Union>x\<in>A. f ` B x)"
  shows "(\<Squnion>z \<in> \<Union>x\<in>A. B x. f z) = (\<Squnion>x\<in>A. \<Squnion>z\<in>B x. f z)"
proof -
  have bdd: "\<And>x. x \<in> A \<Longrightarrow> bdd_above (f ` B x)"
    using bdd_UN by (meson UN_upper bdd_above_mono)
  obtain M where "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B(x) \<Longrightarrow> f y \<le> M"
    using bdd_UN by (auto simp: bdd_above_def)
  then have bdd2: "bdd_above ((\<lambda>x. \<Squnion>z\<in>B x. f z) ` A)"
    unfolding bdd_above_def by (force simp: bdd cSUP_le_iff ne(2))
  have "(\<Squnion>z \<in> \<Union>x\<in>A. B x. f z) \<le> (\<Squnion>x\<in>A. \<Squnion>z\<in>B x. f z)"
    using assms by (fastforce simp add: intro!: cSUP_least intro: cSUP_upper2 simp: bdd2 bdd)
  moreover have "(\<Squnion>x\<in>A. \<Squnion>z\<in>B x. f z) \<le> (\<Squnion> z \<in> \<Union>x\<in>A. B x. f z)"
    using assms by (fastforce simp add: intro!: cSUP_least intro: cSUP_upper simp: image_UN bdd_UN)
  ultimately show ?thesis
    by (rule order_antisym)
qed

lemma cINF_UNION:
  fixes f :: "_ \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes ne: "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> B(x) \<noteq> {}"
      and bdd_UN: "bdd_below (\<Union>x\<in>A. f ` B x)"
  shows "(\<Sqinter>z \<in> \<Union>x\<in>A. B x. f z) = (\<Sqinter>x\<in>A. \<Sqinter>z\<in>B x. f z)"
proof -
  have bdd: "\<And>x. x \<in> A \<Longrightarrow> bdd_below (f ` B x)"
    using bdd_UN by (meson UN_upper bdd_below_mono)
  obtain M where "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B(x) \<Longrightarrow> f y \<ge> M"
    using bdd_UN by (auto simp: bdd_below_def)
  then have bdd2: "bdd_below ((\<lambda>x. \<Sqinter>z\<in>B x. f z) ` A)"
    unfolding bdd_below_def by (force simp: bdd le_cINF_iff ne(2))
  have "(\<Sqinter>z \<in> \<Union>x\<in>A. B x. f z) \<le> (\<Sqinter>x\<in>A. \<Sqinter>z\<in>B x. f z)"
    using assms by (fastforce simp add: intro!: cINF_greatest intro: cINF_lower simp: bdd2 bdd)
  moreover have "(\<Sqinter>x\<in>A. \<Sqinter>z\<in>B x. f z) \<le> (\<Sqinter>z \<in> \<Union>x\<in>A. B x. f z)"
    using assms  by (fastforce simp add: intro!: cINF_greatest intro: cINF_lower2  simp: bdd bdd_UN bdd2)
  ultimately show ?thesis
    by (rule order_antisym)
qed

lemma cSup_abs_le:
  fixes S :: "('a::{linordered_idom,conditionally_complete_linorder}) set"
  shows "S \<noteq> {} \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> \<bar>x\<bar> \<le> a) \<Longrightarrow> \<bar>Sup S\<bar> \<le> a"
  apply (auto simp add: abs_le_iff intro: cSup_least)
  by (metis bdd_aboveI cSup_upper neg_le_iff_le order_trans)

end
