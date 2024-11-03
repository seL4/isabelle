(*  Title:      HOL/Library/Liminf_Limsup.thy
    Author:     Johannes Hölzl, TU München
    Author:     Manuel Eberl, TU München
*)

section \<open>Liminf and Limsup on conditionally complete lattices\<close>

theory Liminf_Limsup
imports Complex_Main
begin

lemma (in conditionally_complete_linorder) le_cSup_iff:
  assumes "A \<noteq> {}" "bdd_above A"
  shows "x \<le> Sup A \<longleftrightarrow> (\<forall>y<x. \<exists>a\<in>A. y < a)"
proof safe
  fix y assume "x \<le> Sup A" "y < x"
  then have "y < Sup A" by auto
  then show "\<exists>a\<in>A. y < a"
    unfolding less_cSup_iff[OF assms] .
qed (auto elim!: allE[of _ "Sup A"] simp add: not_le[symmetric] cSup_upper assms)

lemma (in conditionally_complete_linorder) le_cSUP_iff:
  "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> x \<le> Sup (f ` A) \<longleftrightarrow> (\<forall>y<x. \<exists>i\<in>A. y < f i)"
  using le_cSup_iff [of "f ` A"] by simp

lemma le_cSup_iff_less:
  fixes x :: "'a :: {conditionally_complete_linorder, dense_linorder}"
  shows "A \<noteq> {} \<Longrightarrow> bdd_above (f`A) \<Longrightarrow> x \<le> (SUP i\<in>A. f i) \<longleftrightarrow> (\<forall>y<x. \<exists>i\<in>A. y \<le> f i)"
  by (simp add: le_cSUP_iff)
     (blast intro: less_imp_le less_trans less_le_trans dest: dense)

lemma le_Sup_iff_less:
  fixes x :: "'a :: {complete_linorder, dense_linorder}"
  shows "x \<le> (SUP i\<in>A. f i) \<longleftrightarrow> (\<forall>y<x. \<exists>i\<in>A. y \<le> f i)" (is "?lhs = ?rhs")
  unfolding le_SUP_iff
  by (blast intro: less_imp_le less_trans less_le_trans dest: dense)

lemma (in conditionally_complete_linorder) cInf_le_iff:
  assumes "A \<noteq> {}" "bdd_below A"
  shows "Inf A \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>a\<in>A. y > a)"
proof safe
  fix y assume "x \<ge> Inf A" "y > x"
  then have "y > Inf A" by auto
  then show "\<exists>a\<in>A. y > a"
    unfolding cInf_less_iff[OF assms] .
qed (auto elim!: allE[of _ "Inf A"] simp add: not_le[symmetric] cInf_lower assms)

lemma (in conditionally_complete_linorder) cINF_le_iff:
  "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> Inf (f ` A) \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>i\<in>A. y > f i)"
  using cInf_le_iff [of "f ` A"] by simp

lemma cInf_le_iff_less:
  fixes x :: "'a :: {conditionally_complete_linorder, dense_linorder}"
  shows "A \<noteq> {} \<Longrightarrow> bdd_below (f`A) \<Longrightarrow> (INF i\<in>A. f i) \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>i\<in>A. f i \<le> y)"
  by (simp add: cINF_le_iff)
     (blast intro: less_imp_le less_trans le_less_trans dest: dense)

lemma Inf_le_iff_less:
  fixes x :: "'a :: {complete_linorder, dense_linorder}"
  shows "(INF i\<in>A. f i) \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>i\<in>A. f i \<le> y)"
  unfolding INF_le_iff
  by (blast intro: less_imp_le less_trans le_less_trans dest: dense)

lemma SUP_pair:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: complete_lattice"
  shows "(SUP i \<in> A. SUP j \<in> B. f i j) = (SUP p \<in> A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: SUP_least SUP_upper2)

lemma INF_pair:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: complete_lattice"
  shows "(INF i \<in> A. INF j \<in> B. f i j) = (INF p \<in> A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: INF_greatest INF_lower2)

lemma INF_Sigma:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: complete_lattice"
  shows "(INF i \<in> A. INF j \<in> B i. f i j) = (INF p \<in> Sigma A B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: INF_greatest INF_lower2)

subsubsection \<open>\<open>Liminf\<close> and \<open>Limsup\<close>\<close>

definition Liminf :: "'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b :: complete_lattice" where
  "Liminf F f = (SUP P\<in>{P. eventually P F}. INF x\<in>{x. P x}. f x)"

definition Limsup :: "'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b :: complete_lattice" where
  "Limsup F f = (INF P\<in>{P. eventually P F}. SUP x\<in>{x. P x}. f x)"

abbreviation "liminf \<equiv> Liminf sequentially"

abbreviation "limsup \<equiv> Limsup sequentially"

lemma Liminf_eqI:
  "(\<And>P. eventually P F \<Longrightarrow> Inf (f ` (Collect P)) \<le> x) \<Longrightarrow>
    (\<And>y. (\<And>P. eventually P F \<Longrightarrow> Inf (f ` (Collect P)) \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> Liminf F f = x"
  unfolding Liminf_def by (auto intro!: SUP_eqI)

lemma Limsup_eqI:
  "(\<And>P. eventually P F \<Longrightarrow> x \<le> Sup (f ` (Collect P))) \<Longrightarrow>
    (\<And>y. (\<And>P. eventually P F \<Longrightarrow> y \<le> Sup (f ` (Collect P))) \<Longrightarrow> y \<le> x) \<Longrightarrow> Limsup F f = x"
  unfolding Limsup_def by (auto intro!: INF_eqI)

lemma liminf_SUP_INF: "liminf f = (SUP n. INF m\<in>{n..}. f m)"
  unfolding Liminf_def eventually_sequentially
  by (rule SUP_eq) (auto simp: atLeast_def intro!: INF_mono)

lemma limsup_INF_SUP: "limsup f = (INF n. SUP m\<in>{n..}. f m)"
  unfolding Limsup_def eventually_sequentially
  by (rule INF_eq) (auto simp: atLeast_def intro!: SUP_mono)

lemma mem_limsup_iff: "x \<in> limsup A \<longleftrightarrow> (\<exists>\<^sub>F n in sequentially. x \<in> A n)"
  by (simp add: Limsup_def) (metis (mono_tags) eventually_mono not_frequently)

lemma mem_liminf_iff: "x \<in> liminf A \<longleftrightarrow> (\<forall>\<^sub>F n in sequentially. x \<in> A n)"
  by (simp add: Liminf_def) (metis (mono_tags) eventually_mono)

lemma Limsup_const:
  assumes ntriv: "\<not> trivial_limit F"
  shows "Limsup F (\<lambda>x. c) = c"
proof -
  have *: "\<And>P. Ex P \<longleftrightarrow> P \<noteq> (\<lambda>x. False)" by auto
  have "\<And>P. eventually P F \<Longrightarrow> (SUP x \<in> {x. P x}. c) = c"
    using ntriv by (intro SUP_const) (auto simp: eventually_False *)
  then show ?thesis
    apply (auto simp add: Limsup_def)
    apply (rule INF_const)
    apply auto
    using eventually_True apply blast
    done
qed

lemma Liminf_const:
  assumes ntriv: "\<not> trivial_limit F"
  shows "Liminf F (\<lambda>x. c) = c"
proof -
  have *: "\<And>P. Ex P \<longleftrightarrow> P \<noteq> (\<lambda>x. False)" by auto
  have "\<And>P. eventually P F \<Longrightarrow> (INF x \<in> {x. P x}. c) = c"
    using ntriv by (intro INF_const) (auto simp: eventually_False *)
  then show ?thesis
    apply (auto simp add: Liminf_def)
    apply (rule SUP_const)
    apply auto
    using eventually_True apply blast
    done
qed

lemma Liminf_mono:
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) F"
  shows "Liminf F f \<le> Liminf F g"
  unfolding Liminf_def
proof (safe intro!: SUP_mono)
  fix P assume "eventually P F"
  with ev have "eventually (\<lambda>x. f x \<le> g x \<and> P x) F" (is "eventually ?Q F") by (rule eventually_conj)
  then show "\<exists>Q\<in>{P. eventually P F}. Inf (f ` (Collect P)) \<le> Inf (g ` (Collect Q))"
    by (intro bexI[of _ ?Q]) (auto intro!: INF_mono)
qed

lemma Liminf_eq:
  assumes "eventually (\<lambda>x. f x = g x) F"
  shows "Liminf F f = Liminf F g"
  by (intro antisym Liminf_mono eventually_mono[OF assms]) auto

lemma Limsup_mono:
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) F"
  shows "Limsup F f \<le> Limsup F g"
  unfolding Limsup_def
proof (safe intro!: INF_mono)
  fix P assume "eventually P F"
  with ev have "eventually (\<lambda>x. f x \<le> g x \<and> P x) F" (is "eventually ?Q F") by (rule eventually_conj)
  then show "\<exists>Q\<in>{P. eventually P F}. Sup (f ` (Collect Q)) \<le> Sup (g ` (Collect P))"
    by (intro bexI[of _ ?Q]) (auto intro!: SUP_mono)
qed

lemma Limsup_eq:
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Limsup net f = Limsup net g"
  by (intro antisym Limsup_mono eventually_mono[OF assms]) auto

lemma Liminf_bot[simp]: "Liminf bot f = top"
  unfolding Liminf_def top_unique[symmetric]
  by (rule SUP_upper2[where i="\<lambda>x. False"]) simp_all

lemma Limsup_bot[simp]: "Limsup bot f = bot"
  unfolding Limsup_def bot_unique[symmetric]
  by (rule INF_lower2[where i="\<lambda>x. False"]) simp_all

lemma Liminf_le_Limsup:
  assumes ntriv: "\<not> trivial_limit F"
  shows "Liminf F f \<le> Limsup F f"
  unfolding Limsup_def Liminf_def
  apply (rule SUP_least)
  apply (rule INF_greatest)
proof safe
  fix P Q assume "eventually P F" "eventually Q F"
  then have "eventually (\<lambda>x. P x \<and> Q x) F" (is "eventually ?C F") by (rule eventually_conj)
  then have not_False: "(\<lambda>x. P x \<and> Q x) \<noteq> (\<lambda>x. False)"
    using ntriv by (auto simp add: eventually_False)
  have "Inf (f ` (Collect P)) \<le> Inf (f ` (Collect ?C))"
    by (rule INF_mono) auto
  also have "\<dots> \<le> Sup (f ` (Collect ?C))"
    using not_False by (intro INF_le_SUP) auto
  also have "\<dots> \<le> Sup (f ` (Collect Q))"
    by (rule SUP_mono) auto
  finally show "Inf (f ` (Collect P)) \<le> Sup (f ` (Collect Q))" .
qed

lemma Liminf_bounded:
  assumes le: "eventually (\<lambda>n. C \<le> X n) F"
  shows "C \<le> Liminf F X"
  using Liminf_mono[OF le] Liminf_const[of F C]
  by (cases "F = bot") simp_all

lemma Limsup_bounded:
  assumes le: "eventually (\<lambda>n. X n \<le> C) F"
  shows "Limsup F X \<le> C"
  using Limsup_mono[OF le] Limsup_const[of F C]
  by (cases "F = bot") simp_all

lemma le_Limsup:
  assumes F: "F \<noteq> bot" and x: "\<forall>\<^sub>F x in F. l \<le> f x"
  shows "l \<le> Limsup F f"
  using F Liminf_bounded[of l f F] Liminf_le_Limsup[of F f] order.trans x by blast

lemma Liminf_le:
  assumes F: "F \<noteq> bot" and x: "\<forall>\<^sub>F x in F. f x \<le> l"
  shows "Liminf F f \<le> l"
  using F Liminf_le_Limsup Limsup_bounded order.trans x by blast

lemma le_Liminf_iff:
  fixes X :: "_ \<Rightarrow> _ :: complete_linorder"
  shows "C \<le> Liminf F X \<longleftrightarrow> (\<forall>y<C. eventually (\<lambda>x. y < X x) F)"
proof -
  have "eventually (\<lambda>x. y < X x) F"
    if "eventually P F" "y < Inf (X ` (Collect P))" for y P
    using that by (auto elim!: eventually_mono dest: less_INF_D)
  moreover
  have "\<exists>P. eventually P F \<and> y < Inf (X ` (Collect P))"
    if "y < C" and y: "\<forall>y<C. eventually (\<lambda>x. y < X x) F" for y P
  proof (cases "\<exists>z. y < z \<and> z < C")
    case True
    then obtain z where z: "y < z \<and> z < C" ..
    moreover from z have "z \<le> Inf (X ` {x. z < X x})"
      by (auto intro!: INF_greatest)
    ultimately show ?thesis
      using y by (intro exI[of _ "\<lambda>x. z < X x"]) auto
  next
    case False
    then have "C \<le> Inf (X ` {x. y < X x})"
      by (intro INF_greatest) auto
    with \<open>y < C\<close> show ?thesis
      using y by (intro exI[of _ "\<lambda>x. y < X x"]) auto
  qed
  ultimately show ?thesis
    unfolding Liminf_def le_SUP_iff by auto
qed

lemma Limsup_le_iff:
  fixes X :: "_ \<Rightarrow> _ :: complete_linorder"
  shows "C \<ge> Limsup F X \<longleftrightarrow> (\<forall>y>C. eventually (\<lambda>x. y > X x) F)"
proof -
  { fix y P assume "eventually P F" "y > Sup (X ` (Collect P))"
    then have "eventually (\<lambda>x. y > X x) F"
      by (auto elim!: eventually_mono dest: SUP_lessD) }
  moreover
  { fix y P assume "y > C" and y: "\<forall>y>C. eventually (\<lambda>x. y > X x) F"
    have "\<exists>P. eventually P F \<and> y > Sup (X ` (Collect P))"
    proof (cases "\<exists>z. C < z \<and> z < y")
      case True
      then obtain z where z: "C < z \<and> z < y" ..
      moreover from z have "z \<ge> Sup (X ` {x. X x < z})"
        by (auto intro!: SUP_least)
      ultimately show ?thesis
        using y by (intro exI[of _ "\<lambda>x. z > X x"]) auto
    next
      case False
      then have "C \<ge> Sup (X ` {x. X x < y})"
        by (intro SUP_least) (auto simp: not_less)
      with \<open>y > C\<close> show ?thesis
        using y by (intro exI[of _ "\<lambda>x. y > X x"]) auto
    qed }
  ultimately show ?thesis
    unfolding Limsup_def INF_le_iff by auto
qed

lemma less_LiminfD:
  "y < Liminf F (f :: _ \<Rightarrow> 'a :: complete_linorder) \<Longrightarrow> eventually (\<lambda>x. f x > y) F"
  using le_Liminf_iff[of "Liminf F f" F f] by simp

lemma Limsup_lessD:
  "y > Limsup F (f :: _ \<Rightarrow> 'a :: complete_linorder) \<Longrightarrow> eventually (\<lambda>x. f x < y) F"
  using Limsup_le_iff[of F f "Limsup F f"] by simp

lemma lim_imp_Liminf:
  fixes f :: "'a \<Rightarrow> _ :: {complete_linorder,linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
  assumes lim: "(f \<longlongrightarrow> f0) F"
  shows "Liminf F f = f0"
proof (intro Liminf_eqI)
  fix P assume P: "eventually P F"
  then have "eventually (\<lambda>x. Inf (f ` (Collect P)) \<le> f x) F"
    by eventually_elim (auto intro!: INF_lower)
  then show "Inf (f ` (Collect P)) \<le> f0"
    by (rule tendsto_le[OF ntriv lim tendsto_const])
next
  fix y assume upper: "\<And>P. eventually P F \<Longrightarrow> Inf (f ` (Collect P)) \<le> y"
  show "f0 \<le> y"
  proof cases
    assume "\<exists>z. y < z \<and> z < f0"
    then obtain z where "y < z \<and> z < f0" ..
    moreover have "z \<le> Inf (f ` {x. z < f x})"
      by (rule INF_greatest) simp
    ultimately show ?thesis
      using lim[THEN topological_tendstoD, THEN upper, of "{z <..}"] by auto
  next
    assume discrete: "\<not> (\<exists>z. y < z \<and> z < f0)"
    show ?thesis
    proof (rule classical)
      assume "\<not> f0 \<le> y"
      then have "eventually (\<lambda>x. y < f x) F"
        using lim[THEN topological_tendstoD, of "{y <..}"] by auto
      then have "eventually (\<lambda>x. f0 \<le> f x) F"
        using discrete by (auto elim!: eventually_mono)
      then have "Inf (f ` {x. f0 \<le> f x}) \<le> y"
        by (rule upper)
      moreover have "f0 \<le> Inf (f ` {x. f0 \<le> f x})"
        by (intro INF_greatest) simp
      ultimately show "f0 \<le> y" by simp
    qed
  qed
qed

lemma lim_imp_Limsup:
  fixes f :: "'a \<Rightarrow> _ :: {complete_linorder,linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
  assumes lim: "(f \<longlongrightarrow> f0) F"
  shows "Limsup F f = f0"
proof (intro Limsup_eqI)
  fix P assume P: "eventually P F"
  then have "eventually (\<lambda>x. f x \<le> Sup (f ` (Collect P))) F"
    by eventually_elim (auto intro!: SUP_upper)
  then show "f0 \<le> Sup (f ` (Collect P))"
    by (rule tendsto_le[OF ntriv tendsto_const lim])
next
  fix y assume lower: "\<And>P. eventually P F \<Longrightarrow> y \<le> Sup (f ` (Collect P))"
  show "y \<le> f0"
  proof (cases "\<exists>z. f0 < z \<and> z < y")
    case True
    then obtain z where "f0 < z \<and> z < y" ..
    moreover have "Sup (f ` {x. f x < z}) \<le> z"
      by (rule SUP_least) simp
    ultimately show ?thesis
      using lim[THEN topological_tendstoD, THEN lower, of "{..< z}"] by auto
  next
    case False
    show ?thesis
    proof (rule classical)
      assume "\<not> y \<le> f0"
      then have "eventually (\<lambda>x. f x < y) F"
        using lim[THEN topological_tendstoD, of "{..< y}"] by auto
      then have "eventually (\<lambda>x. f x \<le> f0) F"
        using False by (auto elim!: eventually_mono simp: not_less)
      then have "y \<le> Sup (f ` {x. f x \<le> f0})"
        by (rule lower)
      moreover have "Sup (f ` {x. f x \<le> f0}) \<le> f0"
        by (intro SUP_least) simp
      ultimately show "y \<le> f0" by simp
    qed
  qed
qed

lemma Liminf_eq_Limsup:
  fixes f0 :: "'a :: {complete_linorder,linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
    and lim: "Liminf F f = f0" "Limsup F f = f0"
  shows "(f \<longlongrightarrow> f0) F"
proof (rule order_tendstoI)
  fix a assume "f0 < a"
  with assms have "Limsup F f < a" by simp
  then obtain P where "eventually P F" "Sup (f ` (Collect P)) < a"
    unfolding Limsup_def INF_less_iff by auto
  then show "eventually (\<lambda>x. f x < a) F"
    by (auto elim!: eventually_mono dest: SUP_lessD)
next
  fix a assume "a < f0"
  with assms have "a < Liminf F f" by simp
  then obtain P where "eventually P F" "a < Inf (f ` (Collect P))"
    unfolding Liminf_def less_SUP_iff by auto
  then show "eventually (\<lambda>x. a < f x) F"
    by (auto elim!: eventually_mono dest: less_INF_D)
qed

lemma tendsto_iff_Liminf_eq_Limsup:
  fixes f0 :: "'a :: {complete_linorder,linorder_topology}"
  shows "\<not> trivial_limit F \<Longrightarrow> (f \<longlongrightarrow> f0) F \<longleftrightarrow> (Liminf F f = f0 \<and> Limsup F f = f0)"
  by (metis Liminf_eq_Limsup lim_imp_Limsup lim_imp_Liminf)

lemma liminf_subseq_mono:
  fixes X :: "nat \<Rightarrow> 'a :: complete_linorder"
  assumes "strict_mono r"
  shows "liminf X \<le> liminf (X \<circ> r) "
proof-
  have "\<And>n. (INF m\<in>{n..}. X m) \<le> (INF m\<in>{n..}. (X \<circ> r) m)"
  proof (safe intro!: INF_mono)
    fix n m :: nat assume "n \<le> m" then show "\<exists>ma\<in>{n..}. X ma \<le> (X \<circ> r) m"
      using seq_suble[OF \<open>strict_mono r\<close>, of m] by (intro bexI[of _ "r m"]) auto
  qed
  then show ?thesis by (auto intro!: SUP_mono simp: liminf_SUP_INF comp_def)
qed

lemma limsup_subseq_mono:
  fixes X :: "nat \<Rightarrow> 'a :: complete_linorder"
  assumes "strict_mono r"
  shows "limsup (X \<circ> r) \<le> limsup X"
proof-
  have "(SUP m\<in>{n..}. (X \<circ> r) m) \<le> (SUP m\<in>{n..}. X m)" for n
  proof (safe intro!: SUP_mono)
    fix m :: nat
    assume "n \<le> m"
    then show "\<exists>ma\<in>{n..}. (X \<circ> r) m \<le> X ma"
      using seq_suble[OF \<open>strict_mono r\<close>, of m] by (intro bexI[of _ "r m"]) auto
  qed
  then show ?thesis
    by (auto intro!: INF_mono simp: limsup_INF_SUP comp_def)
qed

lemma continuous_on_imp_continuous_within:
  "continuous_on s f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> x \<in> s \<Longrightarrow> continuous (at x within t) f"
  unfolding continuous_on_eq_continuous_within
  by (auto simp: continuous_within intro: tendsto_within_subset)

lemma Liminf_compose_continuous_mono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "mono f" and F: "F \<noteq> bot"
  shows "Liminf F (\<lambda>n. f (g n)) = f (Liminf F g)"
proof -
  have *: "\<exists>x. P x" if "eventually P F" for P
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "P = (\<lambda>x. False)"
      by auto
    with \<open>eventually P F\<close> F show False
      by auto
  qed
  have "f (SUP P\<in>{P. eventually P F}. Inf (g ` Collect P)) =
    Sup (f ` (\<lambda>P. Inf (g ` Collect P)) ` {P. eventually P F})"
    using am continuous_on_imp_continuous_within [OF c]
    by (rule continuous_at_Sup_mono) (auto intro: eventually_True)
  then have "f (Liminf F g) = (SUP P \<in> {P. eventually P F}. f (Inf (g ` Collect P)))"
    by (simp add: Liminf_def image_comp)
  also have "\<dots> = (SUP P \<in> {P. eventually P F}. Inf (f ` (g ` Collect P)))"
    using * continuous_at_Inf_mono [OF am continuous_on_imp_continuous_within [OF c]]
    by auto
  finally show ?thesis by (auto simp: Liminf_def image_comp)
qed

lemma Limsup_compose_continuous_mono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "mono f" and F: "F \<noteq> bot"
  shows "Limsup F (\<lambda>n. f (g n)) = f (Limsup F g)"
proof -
  have *: "\<exists>x. P x" if "eventually P F" for P
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "P = (\<lambda>x. False)"
      by auto
    with \<open>eventually P F\<close> F show False
      by auto
  qed
  have "f (INF P\<in>{P. eventually P F}. Sup (g ` Collect P)) =
    Inf (f ` (\<lambda>P. Sup (g ` Collect P)) ` {P. eventually P F})"
    using am continuous_on_imp_continuous_within [OF c]
    by (rule continuous_at_Inf_mono) (auto intro: eventually_True)
  then have "f (Limsup F g) = (INF P \<in> {P. eventually P F}. f (Sup (g ` Collect P)))"
    by (simp add: Limsup_def image_comp)
  also have "\<dots> = (INF P \<in> {P. eventually P F}. Sup (f ` (g ` Collect P)))"
    using * continuous_at_Sup_mono [OF am continuous_on_imp_continuous_within [OF c]]
    by auto
  finally show ?thesis by (auto simp: Limsup_def image_comp)
qed

lemma Liminf_compose_continuous_antimono:
  fixes f :: "'a::{complete_linorder,linorder_topology} \<Rightarrow> 'b::{complete_linorder,linorder_topology}"
  assumes c: "continuous_on UNIV f"
    and am: "antimono f"
    and F: "F \<noteq> bot"
  shows "Liminf F (\<lambda>n. f (g n)) = f (Limsup F g)"
proof -
  have *: "\<exists>x. P x" if "eventually P F" for P
  proof (rule ccontr)
    assume "\<not> (\<exists>x. P x)" then have "P = (\<lambda>x. False)"
      by auto
    with \<open>eventually P F\<close> F show False
      by auto
  qed

  have "f (INF P\<in>{P. eventually P F}. Sup (g ` Collect P)) =
    Sup (f ` (\<lambda>P. Sup (g ` Collect P)) ` {P. eventually P F})"
    using am continuous_on_imp_continuous_within [OF c]
    by (rule continuous_at_Inf_antimono) (auto intro: eventually_True)
  then have "f (Limsup F g) = (SUP P \<in> {P. eventually P F}. f (Sup (g ` Collect P)))"
    by (simp add: Limsup_def image_comp)
  also have "\<dots> = (SUP P \<in> {P. eventually P F}. Inf (f ` (g ` Collect P)))"
    using * continuous_at_Sup_antimono [OF am continuous_on_imp_continuous_within [OF c]]
    by auto
  finally show ?thesis
    by (auto simp: Liminf_def image_comp)
qed

lemma Limsup_compose_continuous_antimono:
  fixes f :: "'a::{complete_linorder, linorder_topology} \<Rightarrow> 'b::{complete_linorder, linorder_topology}"
  assumes c: "continuous_on UNIV f" and am: "antimono f" and F: "F \<noteq> bot"
  shows "Limsup F (\<lambda>n. f (g n)) = f (Liminf F g)"
proof -
  have *: "\<exists>x. P x" if "eventually P F" for P
  proof (rule ccontr)
    assume "\<not> (\<exists>x. P x)" then have "P = (\<lambda>x. False)"
      by auto
    with \<open>eventually P F\<close> F show False
      by auto
  qed
  have "f (SUP P\<in>{P. eventually P F}. Inf (g ` Collect P)) =
    Inf (f ` (\<lambda>P. Inf (g ` Collect P)) ` {P. eventually P F})"
    using am continuous_on_imp_continuous_within [OF c]
    by (rule continuous_at_Sup_antimono) (auto intro: eventually_True)
  then have "f (Liminf F g) = (INF P \<in> {P. eventually P F}. f (Inf (g ` Collect P)))"
    by (simp add: Liminf_def image_comp)
  also have "\<dots> = (INF P \<in> {P. eventually P F}. Sup (f ` (g ` Collect P)))"
    using * continuous_at_Inf_antimono [OF am continuous_on_imp_continuous_within [OF c]]
    by auto
  finally show ?thesis
    by (auto simp: Limsup_def image_comp)
qed

lemma Liminf_filtermap_le: "Liminf (filtermap f F) g \<le> Liminf F (\<lambda>x. g (f x))"
  apply (cases "F = bot", simp)
  by (subst Liminf_def)
    (auto simp add: INF_lower Liminf_bounded eventually_filtermap eventually_mono intro!: SUP_least)

lemma Limsup_filtermap_ge: "Limsup (filtermap f F) g \<ge> Limsup F (\<lambda>x. g (f x))"
  apply (cases "F = bot", simp)
  by (subst Limsup_def)
    (auto simp add: SUP_upper Limsup_bounded eventually_filtermap eventually_mono intro!: INF_greatest)

lemma Liminf_least: "(\<And>P. eventually P F \<Longrightarrow> (INF x\<in>Collect P. f x) \<le> x) \<Longrightarrow> Liminf F f \<le> x"
  by (auto intro!: SUP_least simp: Liminf_def)

lemma Limsup_greatest: "(\<And>P. eventually P F \<Longrightarrow> x \<le> (SUP x\<in>Collect P. f x)) \<Longrightarrow> Limsup F f \<ge> x"
  by (auto intro!: INF_greatest simp: Limsup_def)

lemma Liminf_filtermap_ge: "inj f \<Longrightarrow> Liminf (filtermap f F) g \<ge> Liminf F (\<lambda>x. g (f x))"
  apply (cases "F = bot", simp)
  apply (rule Liminf_least)
  subgoal for P
    by (auto simp: eventually_filtermap the_inv_f_f
        intro!: Liminf_bounded INF_lower2 eventually_mono[of P])
  done

lemma Limsup_filtermap_le: "inj f \<Longrightarrow> Limsup (filtermap f F) g \<le> Limsup F (\<lambda>x. g (f x))"
  apply (cases "F = bot", simp)
  apply (rule Limsup_greatest)
  subgoal for P
    by (auto simp: eventually_filtermap the_inv_f_f
        intro!: Limsup_bounded SUP_upper2 eventually_mono[of P])
  done

lemma Liminf_filtermap_eq: "inj f \<Longrightarrow> Liminf (filtermap f F) g = Liminf F (\<lambda>x. g (f x))"
  using Liminf_filtermap_le[of f F g] Liminf_filtermap_ge[of f F g]
  by simp

lemma Limsup_filtermap_eq: "inj f \<Longrightarrow> Limsup (filtermap f F) g = Limsup F (\<lambda>x. g (f x))"
  using Limsup_filtermap_le[of f F g] Limsup_filtermap_ge[of F g f]
  by simp


subsection \<open>More Limits\<close>

lemma convergent_limsup_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> limsup X = lim X"
  by (auto simp: convergent_def limI lim_imp_Limsup)

lemma convergent_liminf_cl:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "convergent X \<Longrightarrow> liminf X = lim X"
  by (auto simp: convergent_def limI lim_imp_Liminf)

lemma lim_increasing_cl:
  assumes "\<And>n m. n \<ge> m \<Longrightarrow> f n \<ge> f m"
  obtains l where "f \<longlonglongrightarrow> (l::'a::{complete_linorder,linorder_topology})"
proof
  show "f \<longlonglongrightarrow> (SUP n. f n)"
    using assms
    by (intro increasing_tendsto)
       (auto simp: SUP_upper eventually_sequentially less_SUP_iff intro: less_le_trans)
qed

lemma lim_decreasing_cl:
  assumes "\<And>n m. n \<ge> m \<Longrightarrow> f n \<le> f m"
  obtains l where "f \<longlonglongrightarrow> (l::'a::{complete_linorder,linorder_topology})"
proof
  show "f \<longlonglongrightarrow> (INF n. f n)"
    using assms
    by (intro decreasing_tendsto)
       (auto simp: INF_lower eventually_sequentially INF_less_iff intro: le_less_trans)
qed

lemma compact_complete_linorder:
  fixes X :: "nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  shows "\<exists>l r. strict_mono r \<and> (X \<circ> r) \<longlonglongrightarrow> l"
proof -
  obtain r where "strict_mono r" and mono: "monoseq (X \<circ> r)"
    using seq_monosub[of X]
    unfolding comp_def
    by auto
  then have "(\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) m \<le> (X \<circ> r) n) \<or> (\<forall>n m. m \<le> n \<longrightarrow> (X \<circ> r) n \<le> (X \<circ> r) m)"
    by (auto simp add: monoseq_def)
  then obtain l where "(X \<circ> r) \<longlonglongrightarrow> l"
     using lim_increasing_cl[of "X \<circ> r"] lim_decreasing_cl[of "X \<circ> r"]
     by auto
  then show ?thesis
    using \<open>strict_mono r\<close> by auto
qed

lemma tendsto_Limsup:
  fixes f :: "_ \<Rightarrow> 'a :: {complete_linorder,linorder_topology}"
  shows "F \<noteq> bot \<Longrightarrow> Limsup F f = Liminf F f \<Longrightarrow> (f \<longlongrightarrow> Limsup F f) F"
  by (subst tendsto_iff_Liminf_eq_Limsup) auto

lemma tendsto_Liminf:
  fixes f :: "_ \<Rightarrow> 'a :: {complete_linorder,linorder_topology}"
  shows "F \<noteq> bot \<Longrightarrow> Limsup F f = Liminf F f \<Longrightarrow> (f \<longlongrightarrow> Liminf F f) F"
  by (subst tendsto_iff_Liminf_eq_Limsup) auto

end
