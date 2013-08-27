(*  Title:      HOL/Conditionally_Complete_Lattices.thy
    Author:     Amine Chaieb and L C Paulson, University of Cambridge
    Author:     Johannes Hölzl, TU München
*)

header {* Conditionally-complete Lattices *}

theory Conditionally_Complete_Lattices
imports Main Lubs
begin

lemma Sup_fin_eq_Max: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup_fin X = Max X"
  by (induct X rule: finite_ne_induct) (simp_all add: sup_max)

lemma Inf_fin_eq_Min: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf_fin X = Min X"
  by (induct X rule: finite_ne_induct) (simp_all add: inf_min)

text {*

To avoid name classes with the @{class complete_lattice}-class we prefix @{const Sup} and
@{const Inf} in theorem names with c.

*}

class conditionally_complete_lattice = lattice + Sup + Inf +
  assumes cInf_lower: "x \<in> X \<Longrightarrow> (\<And>a. a \<in> X \<Longrightarrow> z \<le> a) \<Longrightarrow> Inf X \<le> x"
    and cInf_greatest: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf X"
  assumes cSup_upper: "x \<in> X \<Longrightarrow> (\<And>a. a \<in> X \<Longrightarrow> a \<le> z) \<Longrightarrow> x \<le> Sup X"
    and cSup_least: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
begin

lemma cSup_eq_maximum: (*REAL_SUP_MAX in HOL4*)
  "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X = z"
  by (blast intro: antisym cSup_upper cSup_least)

lemma cInf_eq_minimum: (*REAL_INF_MIN in HOL4*)
  "z \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X = z"
  by (intro antisym cInf_lower[of z X z] cInf_greatest[of X z]) auto

lemma cSup_le_iff: "S \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> S \<Longrightarrow> a \<le> z) \<Longrightarrow> Sup S \<le> a \<longleftrightarrow> (\<forall>x\<in>S. x \<le> a)"
  by (metis order_trans cSup_upper cSup_least)

lemma le_cInf_iff: "S \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> S \<Longrightarrow> z \<le> a) \<Longrightarrow> a \<le> Inf S \<longleftrightarrow> (\<forall>x\<in>S. a \<le> x)"
  by (metis order_trans cInf_lower cInf_greatest)

lemma cSup_singleton [simp]: "Sup {x} = x"
  by (intro cSup_eq_maximum) auto

lemma cInf_singleton [simp]: "Inf {x} = x"
  by (intro cInf_eq_minimum) auto

lemma cSup_upper2: (*REAL_IMP_LE_SUP in HOL4*)
  "x \<in> X \<Longrightarrow> y \<le> x \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> y \<le> Sup X"
  by (metis cSup_upper order_trans)
 
lemma cInf_lower2:
  "x \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X \<le> y"
  by (metis cInf_lower order_trans)

lemma cSup_upper_EX: "x \<in> X \<Longrightarrow> \<exists>z. \<forall>x. x \<in> X \<longrightarrow> x \<le> z \<Longrightarrow> x \<le> Sup X"
  by (blast intro: cSup_upper)

lemma cInf_lower_EX:  "x \<in> X \<Longrightarrow> \<exists>z. \<forall>x. x \<in> X \<longrightarrow> z \<le> x \<Longrightarrow> Inf X \<le> x"
  by (blast intro: cInf_lower)

lemma cSup_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> x \<le> a"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y"
  shows "Sup X = a"
  by (intro 3 1 antisym cSup_least) (auto intro: 2 1 cSup_upper)

lemma cInf_eq_non_empty:
  assumes 1: "X \<noteq> {}"
  assumes 2: "\<And>x. x \<in> X \<Longrightarrow> a \<le> x"
  assumes 3: "\<And>y. (\<And>x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a"
  shows "Inf X = a"
  by (intro 3 1 antisym cInf_greatest) (auto intro: 2 1 cInf_lower)

lemma cInf_cSup: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf S = Sup {x. \<forall>s\<in>S. x \<le> s}"
  by (rule cInf_eq_non_empty) (auto intro: cSup_upper cSup_least)

lemma cSup_cInf: "S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup S = Inf {x. \<forall>s\<in>S. s \<le> x}"
  by (rule cSup_eq_non_empty) (auto intro: cInf_lower cInf_greatest)

lemma cSup_insert: 
  assumes x: "X \<noteq> {}"
      and z: "\<And>x. x \<in> X \<Longrightarrow> x \<le> z"
  shows "Sup (insert a X) = sup a (Sup X)"
proof (intro cSup_eq_non_empty)
  fix y assume "\<And>x. x \<in> insert a X \<Longrightarrow> x \<le> y" with x show "sup a (Sup X) \<le> y" by (auto intro: cSup_least)
qed (auto intro: le_supI2 z cSup_upper)

lemma cInf_insert: 
  assumes x: "X \<noteq> {}"
      and z: "\<And>x. x \<in> X \<Longrightarrow> z \<le> x"
  shows "Inf (insert a X) = inf a (Inf X)"
proof (intro cInf_eq_non_empty)
  fix y assume "\<And>x. x \<in> insert a X \<Longrightarrow> y \<le> x" with x show "y \<le> inf a (Inf X)" by (auto intro: cInf_greatest)
qed (auto intro: le_infI2 z cInf_lower)

lemma cSup_insert_If: 
  "(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup (insert a X) = (if X = {} then a else sup a (Sup X))"
  using cSup_insert[of X z] by simp

lemma cInf_insert_if: 
  "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf (insert a X) = (if X = {} then a else inf a (Inf X))"
  using cInf_insert[of X z] by simp

lemma le_cSup_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> Sup X"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    apply (cases "X = {}")
    apply simp
    apply (subst cSup_insert[of _ "Sup X"])
    apply (auto intro: le_supI2)
    done
qed simp

lemma cInf_le_finite: "finite X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf X \<le> x"
proof (induct X arbitrary: x rule: finite_induct)
  case (insert x X y) then show ?case
    apply (cases "X = {}")
    apply simp
    apply (subst cInf_insert[of _ "Inf X"])
    apply (auto intro: le_infI2)
    done
qed simp

lemma cSup_eq_Sup_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Sup_fin X"
proof (induct X rule: finite_ne_induct)
  case (insert x X) then show ?case
    using cSup_insert[of X "Sup_fin X" x] le_cSup_finite[of X] by simp
qed simp

lemma cInf_eq_Inf_fin: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Inf_fin X"
proof (induct X rule: finite_ne_induct)
  case (insert x X) then show ?case
    using cInf_insert[of X "Inf_fin X" x] cInf_le_finite[of X] by simp
qed simp

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

end

instance complete_lattice \<subseteq> conditionally_complete_lattice
  by default (auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)

lemma isLub_cSup: 
  "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> (\<exists>b. S *<= b) \<Longrightarrow> isLub UNIV S (Sup S)"
  by  (auto simp add: isLub_def setle_def leastP_def isUb_def
            intro!: setgeI intro: cSup_upper cSup_least)

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

lemma cSup_le: "(S::'a::conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> S *<= b \<Longrightarrow> Sup S \<le> b"
  by (metis cSup_least setle_def)

lemma cInf_ge: "(S::'a :: conditionally_complete_lattice set) \<noteq> {} \<Longrightarrow> b <=* S \<Longrightarrow> Inf S \<ge> b"
  by (metis cInf_greatest setge_def)

class conditionally_complete_linorder = conditionally_complete_lattice + linorder
begin

lemma less_cSup_iff : (*REAL_SUP_LE in HOL4*)
  "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> y < Sup X \<longleftrightarrow> (\<exists>x\<in>X. y < x)"
  by (rule iffI) (metis cSup_least not_less, metis cSup_upper less_le_trans)

lemma cInf_less_iff: "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X < y \<longleftrightarrow> (\<exists>x\<in>X. x < y)"
  by (rule iffI) (metis cInf_greatest not_less, metis cInf_lower le_less_trans)

lemma less_cSupE:
  assumes "y < Sup X" "X \<noteq> {}" obtains x where "x \<in> X" "y < x"
  by (metis cSup_least assms not_le that)

lemma less_cSupD:
  "X \<noteq> {} \<Longrightarrow> z < Sup X \<Longrightarrow> \<exists>x\<in>X. z < x"
  by (metis less_cSup_iff not_leE)

lemma cInf_lessD:
  "X \<noteq> {} \<Longrightarrow> Inf X < z \<Longrightarrow> \<exists>x\<in>X. x < z"
  by (metis cInf_less_iff not_leE)

lemma complete_interval:
  assumes "a < b" and "P a" and "\<not> P b"
  shows "\<exists>c. a \<le> c \<and> c \<le> b \<and> (\<forall>x. a \<le> x \<and> x < c \<longrightarrow> P x) \<and>
             (\<forall>d. (\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x) \<longrightarrow> d \<le> c)"
proof (rule exI [where x = "Sup {d. \<forall>x. a \<le> x & x < d --> P x}"], auto)
  show "a \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
    by (rule cSup_upper [where z=b], auto)
       (metis `a < b` `\<not> P b` linear less_le)
next
  show "Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c} \<le> b"
    apply (rule cSup_least) 
    apply auto
    apply (metis less_le_not_le)
    apply (metis `a<b` `~ P b` linear less_le)
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
      by (rule_tac z="b" in cSup_upper, auto) 
         (metis `a<b` `~ P b` linear less_le)
qed

end

class linear_continuum = conditionally_complete_linorder + dense_linorder +
  assumes UNIV_not_singleton: "\<exists>a b::'a. a \<noteq> b"
begin

lemma ex_gt_or_lt: "\<exists>b. a < b \<or> b < a"
  by (metis UNIV_not_singleton neq_iff)

end

lemma cSup_bounds:
  fixes S :: "'a :: conditionally_complete_lattice set"
  assumes Se: "S \<noteq> {}" and l: "a <=* S" and u: "S *<= b"
  shows "a \<le> Sup S \<and> Sup S \<le> b"
proof-
  from isLub_cSup[OF Se] u have lub: "isLub UNIV S (Sup S)" by blast
  hence b: "Sup S \<le> b" using u 
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def) 
  from Se obtain y where y: "y \<in> S" by blast
  from lub l have "a \<le> Sup S"
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def)
       (metis le_iff_sup le_sup_iff y)
  with b show ?thesis by blast
qed


lemma cSup_unique: "(S::'a :: {conditionally_complete_linorder, no_bot} set) *<= b \<Longrightarrow> (\<forall>b'<b. \<exists>x\<in>S. b' < x) \<Longrightarrow> Sup S = b"
  by (rule cSup_eq) (auto simp: not_le[symmetric] setle_def)

lemma cInf_unique: "b <=* (S::'a :: {conditionally_complete_linorder, no_top} set) \<Longrightarrow> (\<forall>b'>b. \<exists>x\<in>S. b' > x) \<Longrightarrow> Inf S = b"
  by (rule cInf_eq) (auto simp: not_le[symmetric] setge_def)

lemma cSup_eq_Max: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Sup X = Max X"
  using cSup_eq_Sup_fin[of X] Sup_fin_eq_Max[of X] by simp

lemma cInf_eq_Min: "finite (X::'a::conditionally_complete_linorder set) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Inf X = Min X"
  using cInf_eq_Inf_fin[of X] Inf_fin_eq_Min[of X] by simp

lemma cSup_lessThan[simp]: "Sup {..<x::'a::{conditionally_complete_linorder, unbounded_dense_linorder}} = x"
  by (auto intro!: cSup_eq_non_empty intro: dense_le)

lemma cSup_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Sup {y<..<x::'a::{conditionally_complete_linorder, unbounded_dense_linorder}} = x"
  by (auto intro!: cSup_eq intro: dense_le_bounded)

lemma cSup_atLeastLessThan[simp]: "y < x \<Longrightarrow> Sup {y..<x::'a::{conditionally_complete_linorder, unbounded_dense_linorder}} = x"
  by (auto intro!: cSup_eq intro: dense_le_bounded)

lemma cInf_greaterThan[simp]: "Inf {x::'a::{conditionally_complete_linorder, unbounded_dense_linorder} <..} = x"
  by (auto intro!: cInf_eq intro: dense_ge)

lemma cInf_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Inf {y<..x::'a::{conditionally_complete_linorder, unbounded_dense_linorder}} = y"
  by (auto intro!: cInf_eq intro: dense_ge_bounded)

lemma cInf_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Inf {y<..<x::'a::{conditionally_complete_linorder, unbounded_dense_linorder}} = y"
  by (auto intro!: cInf_eq intro: dense_ge_bounded)

end
