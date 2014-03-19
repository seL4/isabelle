(*  Title:      HOL/Library/Liminf_Limsup.thy
    Author:     Johannes Hölzl, TU München
*)

header {* Liminf and Limsup on complete lattices *}

theory Liminf_Limsup
imports Complex_Main
begin

lemma le_Sup_iff_less:
  fixes x :: "'a :: {complete_linorder, dense_linorder}"
  shows "x \<le> (SUP i:A. f i) \<longleftrightarrow> (\<forall>y<x. \<exists>i\<in>A. y \<le> f i)" (is "?lhs = ?rhs")
  unfolding le_SUP_iff
  by (blast intro: less_imp_le less_trans less_le_trans dest: dense)

lemma Inf_le_iff_less:
  fixes x :: "'a :: {complete_linorder, dense_linorder}"
  shows "(INF i:A. f i) \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>i\<in>A. f i \<le> y)"
  unfolding INF_le_iff
  by (blast intro: less_imp_le less_trans le_less_trans dest: dense)

lemma SUP_pair:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: complete_lattice"
  shows "(SUP i : A. SUP j : B. f i j) = (SUP p : A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: SUP_least SUP_upper2)

lemma INF_pair:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> _ :: complete_lattice"
  shows "(INF i : A. INF j : B. f i j) = (INF p : A \<times> B. f (fst p) (snd p))"
  by (rule antisym) (auto intro!: INF_greatest INF_lower2)

subsubsection {* @{text Liminf} and @{text Limsup} *}

definition Liminf :: "'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b :: complete_lattice" where
  "Liminf F f = (SUP P:{P. eventually P F}. INF x:{x. P x}. f x)"

definition Limsup :: "'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b :: complete_lattice" where
  "Limsup F f = (INF P:{P. eventually P F}. SUP x:{x. P x}. f x)"

abbreviation "liminf \<equiv> Liminf sequentially"

abbreviation "limsup \<equiv> Limsup sequentially"

lemma Liminf_eqI:
  "(\<And>P. eventually P F \<Longrightarrow> INFIMUM (Collect P) f \<le> x) \<Longrightarrow>  
    (\<And>y. (\<And>P. eventually P F \<Longrightarrow> INFIMUM (Collect P) f \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> Liminf F f = x"
  unfolding Liminf_def by (auto intro!: SUP_eqI)

lemma Limsup_eqI:
  "(\<And>P. eventually P F \<Longrightarrow> x \<le> SUPREMUM (Collect P) f) \<Longrightarrow>  
    (\<And>y. (\<And>P. eventually P F \<Longrightarrow> y \<le> SUPREMUM (Collect P) f) \<Longrightarrow> y \<le> x) \<Longrightarrow> Limsup F f = x"
  unfolding Limsup_def by (auto intro!: INF_eqI)

lemma liminf_SUP_INF: "liminf f = (SUP n. INF m:{n..}. f m)"
  unfolding Liminf_def eventually_sequentially
  by (rule SUP_eq) (auto simp: atLeast_def intro!: INF_mono)

lemma limsup_INF_SUP: "limsup f = (INF n. SUP m:{n..}. f m)"
  unfolding Limsup_def eventually_sequentially
  by (rule INF_eq) (auto simp: atLeast_def intro!: SUP_mono)

lemma Limsup_const: 
  assumes ntriv: "\<not> trivial_limit F"
  shows "Limsup F (\<lambda>x. c) = c"
proof -
  have *: "\<And>P. Ex P \<longleftrightarrow> P \<noteq> (\<lambda>x. False)" by auto
  have "\<And>P. eventually P F \<Longrightarrow> (SUP x : {x. P x}. c) = c"
    using ntriv by (intro SUP_const) (auto simp: eventually_False *)
  then show ?thesis
    unfolding Limsup_def using eventually_True
    by (subst INF_cong[where D="\<lambda>x. c"])
       (auto intro!: INF_const simp del: eventually_True)
qed

lemma Liminf_const:
  assumes ntriv: "\<not> trivial_limit F"
  shows "Liminf F (\<lambda>x. c) = c"
proof -
  have *: "\<And>P. Ex P \<longleftrightarrow> P \<noteq> (\<lambda>x. False)" by auto
  have "\<And>P. eventually P F \<Longrightarrow> (INF x : {x. P x}. c) = c"
    using ntriv by (intro INF_const) (auto simp: eventually_False *)
  then show ?thesis
    unfolding Liminf_def using eventually_True
    by (subst SUP_cong[where D="\<lambda>x. c"])
       (auto intro!: SUP_const simp del: eventually_True)
qed

lemma Liminf_mono:
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) F"
  shows "Liminf F f \<le> Liminf F g"
  unfolding Liminf_def
proof (safe intro!: SUP_mono)
  fix P assume "eventually P F"
  with ev have "eventually (\<lambda>x. f x \<le> g x \<and> P x) F" (is "eventually ?Q F") by (rule eventually_conj)
  then show "\<exists>Q\<in>{P. eventually P F}. INFIMUM (Collect P) f \<le> INFIMUM (Collect Q) g"
    by (intro bexI[of _ ?Q]) (auto intro!: INF_mono)
qed

lemma Liminf_eq:
  assumes "eventually (\<lambda>x. f x = g x) F"
  shows "Liminf F f = Liminf F g"
  by (intro antisym Liminf_mono eventually_mono[OF _ assms]) auto

lemma Limsup_mono:
  assumes ev: "eventually (\<lambda>x. f x \<le> g x) F"
  shows "Limsup F f \<le> Limsup F g"
  unfolding Limsup_def
proof (safe intro!: INF_mono)
  fix P assume "eventually P F"
  with ev have "eventually (\<lambda>x. f x \<le> g x \<and> P x) F" (is "eventually ?Q F") by (rule eventually_conj)
  then show "\<exists>Q\<in>{P. eventually P F}. SUPREMUM (Collect Q) f \<le> SUPREMUM (Collect P) g"
    by (intro bexI[of _ ?Q]) (auto intro!: SUP_mono)
qed

lemma Limsup_eq:
  assumes "eventually (\<lambda>x. f x = g x) net"
  shows "Limsup net f = Limsup net g"
  by (intro antisym Limsup_mono eventually_mono[OF _ assms]) auto

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
  have "INFIMUM (Collect P) f \<le> INFIMUM (Collect ?C) f"
    by (rule INF_mono) auto
  also have "\<dots> \<le> SUPREMUM (Collect ?C) f"
    using not_False by (intro INF_le_SUP) auto
  also have "\<dots> \<le> SUPREMUM (Collect Q) f"
    by (rule SUP_mono) auto
  finally show "INFIMUM (Collect P) f \<le> SUPREMUM (Collect Q) f" .
qed

lemma Liminf_bounded:
  assumes ntriv: "\<not> trivial_limit F"
  assumes le: "eventually (\<lambda>n. C \<le> X n) F"
  shows "C \<le> Liminf F X"
  using Liminf_mono[OF le] Liminf_const[OF ntriv, of C] by simp

lemma Limsup_bounded:
  assumes ntriv: "\<not> trivial_limit F"
  assumes le: "eventually (\<lambda>n. X n \<le> C) F"
  shows "Limsup F X \<le> C"
  using Limsup_mono[OF le] Limsup_const[OF ntriv, of C] by simp

lemma le_Liminf_iff:
  fixes X :: "_ \<Rightarrow> _ :: complete_linorder"
  shows "C \<le> Liminf F X \<longleftrightarrow> (\<forall>y<C. eventually (\<lambda>x. y < X x) F)"
proof -
  { fix y P assume "eventually P F" "y < INFIMUM (Collect P) X"
    then have "eventually (\<lambda>x. y < X x) F"
      by (auto elim!: eventually_elim1 dest: less_INF_D) }
  moreover
  { fix y P assume "y < C" and y: "\<forall>y<C. eventually (\<lambda>x. y < X x) F"
    have "\<exists>P. eventually P F \<and> y < INFIMUM (Collect P) X"
    proof (cases "\<exists>z. y < z \<and> z < C")
      case True
      then obtain z where z: "y < z \<and> z < C" ..
      moreover from z have "z \<le> INFIMUM {x. z < X x} X"
        by (auto intro!: INF_greatest)
      ultimately show ?thesis
        using y by (intro exI[of _ "\<lambda>x. z < X x"]) auto
    next
      case False
      then have "C \<le> INFIMUM {x. y < X x} X"
        by (intro INF_greatest) auto
      with `y < C` show ?thesis
        using y by (intro exI[of _ "\<lambda>x. y < X x"]) auto
    qed }
  ultimately show ?thesis
    unfolding Liminf_def le_SUP_iff by auto
qed

lemma lim_imp_Liminf:
  fixes f :: "'a \<Rightarrow> _ :: {complete_linorder, linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
  assumes lim: "(f ---> f0) F"
  shows "Liminf F f = f0"
proof (intro Liminf_eqI)
  fix P assume P: "eventually P F"
  then have "eventually (\<lambda>x. INFIMUM (Collect P) f \<le> f x) F"
    by eventually_elim (auto intro!: INF_lower)
  then show "INFIMUM (Collect P) f \<le> f0"
    by (rule tendsto_le[OF ntriv lim tendsto_const])
next
  fix y assume upper: "\<And>P. eventually P F \<Longrightarrow> INFIMUM (Collect P) f \<le> y"
  show "f0 \<le> y"
  proof cases
    assume "\<exists>z. y < z \<and> z < f0"
    then obtain z where "y < z \<and> z < f0" ..
    moreover have "z \<le> INFIMUM {x. z < f x} f"
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
        using discrete by (auto elim!: eventually_elim1)
      then have "INFIMUM {x. f0 \<le> f x} f \<le> y"
        by (rule upper)
      moreover have "f0 \<le> INFIMUM {x. f0 \<le> f x} f"
        by (intro INF_greatest) simp
      ultimately show "f0 \<le> y" by simp
    qed
  qed
qed

lemma lim_imp_Limsup:
  fixes f :: "'a \<Rightarrow> _ :: {complete_linorder, linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
  assumes lim: "(f ---> f0) F"
  shows "Limsup F f = f0"
proof (intro Limsup_eqI)
  fix P assume P: "eventually P F"
  then have "eventually (\<lambda>x. f x \<le> SUPREMUM (Collect P) f) F"
    by eventually_elim (auto intro!: SUP_upper)
  then show "f0 \<le> SUPREMUM (Collect P) f"
    by (rule tendsto_le[OF ntriv tendsto_const lim])
next
  fix y assume lower: "\<And>P. eventually P F \<Longrightarrow> y \<le> SUPREMUM (Collect P) f"
  show "y \<le> f0"
  proof (cases "\<exists>z. f0 < z \<and> z < y")
    case True
    then obtain z where "f0 < z \<and> z < y" ..
    moreover have "SUPREMUM {x. f x < z} f \<le> z"
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
        using False by (auto elim!: eventually_elim1 simp: not_less)
      then have "y \<le> SUPREMUM {x. f x \<le> f0} f"
        by (rule lower)
      moreover have "SUPREMUM {x. f x \<le> f0} f \<le> f0"
        by (intro SUP_least) simp
      ultimately show "y \<le> f0" by simp
    qed
  qed
qed

lemma Liminf_eq_Limsup:
  fixes f0 :: "'a :: {complete_linorder, linorder_topology}"
  assumes ntriv: "\<not> trivial_limit F"
    and lim: "Liminf F f = f0" "Limsup F f = f0"
  shows "(f ---> f0) F"
proof (rule order_tendstoI)
  fix a assume "f0 < a"
  with assms have "Limsup F f < a" by simp
  then obtain P where "eventually P F" "SUPREMUM (Collect P) f < a"
    unfolding Limsup_def INF_less_iff by auto
  then show "eventually (\<lambda>x. f x < a) F"
    by (auto elim!: eventually_elim1 dest: SUP_lessD)
next
  fix a assume "a < f0"
  with assms have "a < Liminf F f" by simp
  then obtain P where "eventually P F" "a < INFIMUM (Collect P) f"
    unfolding Liminf_def less_SUP_iff by auto
  then show "eventually (\<lambda>x. a < f x) F"
    by (auto elim!: eventually_elim1 dest: less_INF_D)
qed

lemma tendsto_iff_Liminf_eq_Limsup:
  fixes f0 :: "'a :: {complete_linorder, linorder_topology}"
  shows "\<not> trivial_limit F \<Longrightarrow> (f ---> f0) F \<longleftrightarrow> (Liminf F f = f0 \<and> Limsup F f = f0)"
  by (metis Liminf_eq_Limsup lim_imp_Limsup lim_imp_Liminf)

lemma liminf_subseq_mono:
  fixes X :: "nat \<Rightarrow> 'a :: complete_linorder"
  assumes "subseq r"
  shows "liminf X \<le> liminf (X \<circ> r) "
proof-
  have "\<And>n. (INF m:{n..}. X m) \<le> (INF m:{n..}. (X \<circ> r) m)"
  proof (safe intro!: INF_mono)
    fix n m :: nat assume "n \<le> m" then show "\<exists>ma\<in>{n..}. X ma \<le> (X \<circ> r) m"
      using seq_suble[OF `subseq r`, of m] by (intro bexI[of _ "r m"]) auto
  qed
  then show ?thesis by (auto intro!: SUP_mono simp: liminf_SUP_INF comp_def)
qed

lemma limsup_subseq_mono:
  fixes X :: "nat \<Rightarrow> 'a :: complete_linorder"
  assumes "subseq r"
  shows "limsup (X \<circ> r) \<le> limsup X"
proof-
  have "\<And>n. (SUP m:{n..}. (X \<circ> r) m) \<le> (SUP m:{n..}. X m)"
  proof (safe intro!: SUP_mono)
    fix n m :: nat assume "n \<le> m" then show "\<exists>ma\<in>{n..}. (X \<circ> r) m \<le> X ma"
      using seq_suble[OF `subseq r`, of m] by (intro bexI[of _ "r m"]) auto
  qed
  then show ?thesis by (auto intro!: INF_mono simp: limsup_INF_SUP comp_def)
qed

end
