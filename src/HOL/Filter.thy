(*  Title:      HOL/Filter.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

section \<open>Filters on predicates\<close>

theory Filter
imports Set_Interval Lifting_Set
begin

subsection \<open>Filters\<close>

text \<open>
  This definition also allows non-proper filters.
\<close>

locale is_filter =
  fixes F :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes True: "F (\<lambda>x. True)"
  assumes conj: "F (\<lambda>x. P x) \<Longrightarrow> F (\<lambda>x. Q x) \<Longrightarrow> F (\<lambda>x. P x \<and> Q x)"
  assumes mono: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> F (\<lambda>x. P x) \<Longrightarrow> F (\<lambda>x. Q x)"

typedef 'a filter = "{F :: ('a \<Rightarrow> bool) \<Rightarrow> bool. is_filter F}"
proof
  show "(\<lambda>x. True) \<in> ?filter" by (auto intro: is_filter.intro)
qed

lemma is_filter_Rep_filter: "is_filter (Rep_filter F)"
  using Rep_filter [of F] by simp

lemma Abs_filter_inverse':
  assumes "is_filter F" shows "Rep_filter (Abs_filter F) = F"
  using assms by (simp add: Abs_filter_inverse)


subsubsection \<open>Eventually\<close>

definition eventually :: "('a \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "eventually P F \<longleftrightarrow> Rep_filter F P"

syntax
  "_eventually" :: "pttrn => 'a filter => bool => bool"  ("(3\<forall>\<^sub>F _ in _./ _)" [0, 0, 10] 10)
translations
  "\<forall>\<^sub>Fx in F. P" == "CONST eventually (\<lambda>x. P) F"

lemma eventually_Abs_filter:
  assumes "is_filter F" shows "eventually P (Abs_filter F) = F P"
  unfolding eventually_def using assms by (simp add: Abs_filter_inverse)

lemma filter_eq_iff:
  shows "F = F' \<longleftrightarrow> (\<forall>P. eventually P F = eventually P F')"
  unfolding Rep_filter_inject [symmetric] fun_eq_iff eventually_def ..

lemma eventually_True [simp]: "eventually (\<lambda>x. True) F"
  unfolding eventually_def
  by (rule is_filter.True [OF is_filter_Rep_filter])

lemma always_eventually: "\<forall>x. P x \<Longrightarrow> eventually P F"
proof -
  assume "\<forall>x. P x" hence "P = (\<lambda>x. True)" by (simp add: ext)
  thus "eventually P F" by simp
qed

lemma eventuallyI: "(\<And>x. P x) \<Longrightarrow> eventually P F"
  by (auto intro: always_eventually)

lemma eventually_mono:
  "\<lbrakk>eventually P F; \<And>x. P x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> eventually Q F"
  unfolding eventually_def
  by (blast intro: is_filter.mono [OF is_filter_Rep_filter])

lemma eventually_conj:
  assumes P: "eventually (\<lambda>x. P x) F"
  assumes Q: "eventually (\<lambda>x. Q x) F"
  shows "eventually (\<lambda>x. P x \<and> Q x) F"
  using assms unfolding eventually_def
  by (rule is_filter.conj [OF is_filter_Rep_filter])

lemma eventually_mp:
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  assumes "eventually (\<lambda>x. P x) F"
  shows "eventually (\<lambda>x. Q x) F"
proof -
  have "eventually (\<lambda>x. (P x \<longrightarrow> Q x) \<and> P x) F"
    using assms by (rule eventually_conj)
  then show ?thesis
    by (blast intro: eventually_mono)
qed

lemma eventually_rev_mp:
  assumes "eventually (\<lambda>x. P x) F"
  assumes "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  shows "eventually (\<lambda>x. Q x) F"
using assms(2) assms(1) by (rule eventually_mp)

lemma eventually_conj_iff:
  "eventually (\<lambda>x. P x \<and> Q x) F \<longleftrightarrow> eventually P F \<and> eventually Q F"
  by (auto intro: eventually_conj elim: eventually_rev_mp)

lemma eventually_elim2:
  assumes "eventually (\<lambda>i. P i) F"
  assumes "eventually (\<lambda>i. Q i) F"
  assumes "\<And>i. P i \<Longrightarrow> Q i \<Longrightarrow> R i"
  shows "eventually (\<lambda>i. R i) F"
  using assms by (auto elim!: eventually_rev_mp)

lemma eventually_ball_finite_distrib:
  "finite A \<Longrightarrow> (eventually (\<lambda>x. \<forall>y\<in>A. P x y) net) \<longleftrightarrow> (\<forall>y\<in>A. eventually (\<lambda>x. P x y) net)"
  by (induction A rule: finite_induct) (auto simp: eventually_conj_iff)

lemma eventually_ball_finite:
  "finite A \<Longrightarrow> \<forall>y\<in>A. eventually (\<lambda>x. P x y) net \<Longrightarrow> eventually (\<lambda>x. \<forall>y\<in>A. P x y) net"
  by (auto simp: eventually_ball_finite_distrib)

lemma eventually_all_finite:
  fixes P :: "'a \<Rightarrow> 'b::finite \<Rightarrow> bool"
  assumes "\<And>y. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y. P x y) net"
using eventually_ball_finite [of UNIV P] assms by simp

lemma eventually_ex: "(\<forall>\<^sub>Fx in F. \<exists>y. P x y) \<longleftrightarrow> (\<exists>Y. \<forall>\<^sub>Fx in F. P x (Y x))"
proof
  assume "\<forall>\<^sub>Fx in F. \<exists>y. P x y"
  then have "\<forall>\<^sub>Fx in F. P x (SOME y. P x y)"
    by (auto intro: someI_ex eventually_mono)
  then show "\<exists>Y. \<forall>\<^sub>Fx in F. P x (Y x)"
    by auto
qed (auto intro: eventually_mono)

lemma not_eventually_impI: "eventually P F \<Longrightarrow> \<not> eventually Q F \<Longrightarrow> \<not> eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
  by (auto intro: eventually_mp)

lemma not_eventuallyD: "\<not> eventually P F \<Longrightarrow> \<exists>x. \<not> P x"
  by (metis always_eventually)

lemma eventually_subst:
  assumes "eventually (\<lambda>n. P n = Q n) F"
  shows "eventually P F = eventually Q F" (is "?L = ?R")
proof -
  from assms have "eventually (\<lambda>x. P x \<longrightarrow> Q x) F"
      and "eventually (\<lambda>x. Q x \<longrightarrow> P x) F"
    by (auto elim: eventually_mono)
  then show ?thesis by (auto elim: eventually_elim2)
qed

subsection \<open> Frequently as dual to eventually \<close>

definition frequently :: "('a \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "frequently P F \<longleftrightarrow> \<not> eventually (\<lambda>x. \<not> P x) F"

syntax
  "_frequently" :: "pttrn \<Rightarrow> 'a filter \<Rightarrow> bool \<Rightarrow> bool"  ("(3\<exists>\<^sub>F _ in _./ _)" [0, 0, 10] 10)
translations
  "\<exists>\<^sub>Fx in F. P" == "CONST frequently (\<lambda>x. P) F"

lemma not_frequently_False [simp]: "\<not> (\<exists>\<^sub>Fx in F. False)"
  by (simp add: frequently_def)

lemma frequently_ex: "\<exists>\<^sub>Fx in F. P x \<Longrightarrow> \<exists>x. P x"
  by (auto simp: frequently_def dest: not_eventuallyD)

lemma frequentlyE: assumes "frequently P F" obtains x where "P x"
  using frequently_ex[OF assms] by auto

lemma frequently_mp:
  assumes ev: "\<forall>\<^sub>Fx in F. P x \<longrightarrow> Q x" and P: "\<exists>\<^sub>Fx in F. P x" shows "\<exists>\<^sub>Fx in F. Q x"
proof -
  from ev have "eventually (\<lambda>x. \<not> Q x \<longrightarrow> \<not> P x) F"
    by (rule eventually_rev_mp) (auto intro!: always_eventually)
  from eventually_mp[OF this] P show ?thesis
    by (auto simp: frequently_def)
qed

lemma frequently_rev_mp:
  assumes "\<exists>\<^sub>Fx in F. P x"
  assumes "\<forall>\<^sub>Fx in F. P x \<longrightarrow> Q x"
  shows "\<exists>\<^sub>Fx in F. Q x"
using assms(2) assms(1) by (rule frequently_mp)

lemma frequently_mono: "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> frequently P F \<Longrightarrow> frequently Q F"
  using frequently_mp[of P Q] by (simp add: always_eventually)

lemma frequently_elim1: "\<exists>\<^sub>Fx in F. P x \<Longrightarrow> (\<And>i. P i \<Longrightarrow> Q i) \<Longrightarrow> \<exists>\<^sub>Fx in F. Q x"
  by (metis frequently_mono)

lemma frequently_disj_iff: "(\<exists>\<^sub>Fx in F. P x \<or> Q x) \<longleftrightarrow> (\<exists>\<^sub>Fx in F. P x) \<or> (\<exists>\<^sub>Fx in F. Q x)"
  by (simp add: frequently_def eventually_conj_iff)

lemma frequently_disj: "\<exists>\<^sub>Fx in F. P x \<Longrightarrow> \<exists>\<^sub>Fx in F. Q x \<Longrightarrow> \<exists>\<^sub>Fx in F. P x \<or> Q x"
  by (simp add: frequently_disj_iff)

lemma frequently_bex_finite_distrib:
  assumes "finite A" shows "(\<exists>\<^sub>Fx in F. \<exists>y\<in>A. P x y) \<longleftrightarrow> (\<exists>y\<in>A. \<exists>\<^sub>Fx in F. P x y)"
  using assms by induction (auto simp: frequently_disj_iff)

lemma frequently_bex_finite: "finite A \<Longrightarrow> \<exists>\<^sub>Fx in F. \<exists>y\<in>A. P x y \<Longrightarrow> \<exists>y\<in>A. \<exists>\<^sub>Fx in F. P x y"
  by (simp add: frequently_bex_finite_distrib)

lemma frequently_all: "(\<exists>\<^sub>Fx in F. \<forall>y. P x y) \<longleftrightarrow> (\<forall>Y. \<exists>\<^sub>Fx in F. P x (Y x))"
  using eventually_ex[of "\<lambda>x y. \<not> P x y" F] by (simp add: frequently_def)

lemma
  shows not_eventually: "\<not> eventually P F \<longleftrightarrow> (\<exists>\<^sub>Fx in F. \<not> P x)"
    and not_frequently: "\<not> frequently P F \<longleftrightarrow> (\<forall>\<^sub>Fx in F. \<not> P x)"
  by (auto simp: frequently_def)

lemma frequently_imp_iff:
  "(\<exists>\<^sub>Fx in F. P x \<longrightarrow> Q x) \<longleftrightarrow> (eventually P F \<longrightarrow> frequently Q F)"
  unfolding imp_conv_disj frequently_disj_iff not_eventually[symmetric] ..

lemma eventually_frequently_const_simps:
  "(\<exists>\<^sub>Fx in F. P x \<and> C) \<longleftrightarrow> (\<exists>\<^sub>Fx in F. P x) \<and> C"
  "(\<exists>\<^sub>Fx in F. C \<and> P x) \<longleftrightarrow> C \<and> (\<exists>\<^sub>Fx in F. P x)"
  "(\<forall>\<^sub>Fx in F. P x \<or> C) \<longleftrightarrow> (\<forall>\<^sub>Fx in F. P x) \<or> C"
  "(\<forall>\<^sub>Fx in F. C \<or> P x) \<longleftrightarrow> C \<or> (\<forall>\<^sub>Fx in F. P x)"
  "(\<forall>\<^sub>Fx in F. P x \<longrightarrow> C) \<longleftrightarrow> ((\<exists>\<^sub>Fx in F. P x) \<longrightarrow> C)"
  "(\<forall>\<^sub>Fx in F. C \<longrightarrow> P x) \<longleftrightarrow> (C \<longrightarrow> (\<forall>\<^sub>Fx in F. P x))"
  by (cases C; simp add: not_frequently)+

lemmas eventually_frequently_simps =
  eventually_frequently_const_simps
  not_eventually
  eventually_conj_iff
  eventually_ball_finite_distrib
  eventually_ex
  not_frequently
  frequently_disj_iff
  frequently_bex_finite_distrib
  frequently_all
  frequently_imp_iff

ML \<open>
  fun eventually_elim_tac facts =
    CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
      let
        val mp_facts = facts RL @{thms eventually_rev_mp}
        val rule =
          @{thm eventuallyI}
          |> fold (fn mp_fact => fn th => th RS mp_fact) mp_facts
          |> funpow (length facts) (fn th => @{thm impI} RS th)
        val cases_prop =
          Thm.prop_of (Rule_Cases.internalize_params (rule RS Goal.init (Thm.cterm_of ctxt goal)))
        val cases = Rule_Cases.make_common ctxt cases_prop [(("elim", []), [])]
      in CONTEXT_CASES cases (resolve_tac ctxt [rule] i) (ctxt, st) end)
\<close>

method_setup eventually_elim = \<open>
  Scan.succeed (fn _ => CONTEXT_METHOD (fn facts => eventually_elim_tac facts 1))
\<close> "elimination of eventually quantifiers"

subsubsection \<open>Finer-than relation\<close>

text \<open>@{term "F \<le> F'"} means that filter @{term F} is finer than
filter @{term F'}.\<close>

instantiation filter :: (type) complete_lattice
begin

definition le_filter_def:
  "F \<le> F' \<longleftrightarrow> (\<forall>P. eventually P F' \<longrightarrow> eventually P F)"

definition
  "(F :: 'a filter) < F' \<longleftrightarrow> F \<le> F' \<and> \<not> F' \<le> F"

definition
  "top = Abs_filter (\<lambda>P. \<forall>x. P x)"

definition
  "bot = Abs_filter (\<lambda>P. True)"

definition
  "sup F F' = Abs_filter (\<lambda>P. eventually P F \<and> eventually P F')"

definition
  "inf F F' = Abs_filter
      (\<lambda>P. \<exists>Q R. eventually Q F \<and> eventually R F' \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"

definition
  "Sup S = Abs_filter (\<lambda>P. \<forall>F\<in>S. eventually P F)"

definition
  "Inf S = Sup {F::'a filter. \<forall>F'\<in>S. F \<le> F'}"

lemma eventually_top [simp]: "eventually P top \<longleftrightarrow> (\<forall>x. P x)"
  unfolding top_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_bot [simp]: "eventually P bot"
  unfolding bot_filter_def
  by (subst eventually_Abs_filter, rule is_filter.intro, auto)

lemma eventually_sup:
  "eventually P (sup F F') \<longleftrightarrow> eventually P F \<and> eventually P F'"
  unfolding sup_filter_def
  by (rule eventually_Abs_filter, rule is_filter.intro)
     (auto elim!: eventually_rev_mp)

lemma eventually_inf:
  "eventually P (inf F F') \<longleftrightarrow>
   (\<exists>Q R. eventually Q F \<and> eventually R F' \<and> (\<forall>x. Q x \<and> R x \<longrightarrow> P x))"
  unfolding inf_filter_def
  apply (rule eventually_Abs_filter, rule is_filter.intro)
  apply (fast intro: eventually_True)
  apply clarify
  apply (intro exI conjI)
  apply (erule (1) eventually_conj)
  apply (erule (1) eventually_conj)
  apply simp
  apply auto
  done

lemma eventually_Sup:
  "eventually P (Sup S) \<longleftrightarrow> (\<forall>F\<in>S. eventually P F)"
  unfolding Sup_filter_def
  apply (rule eventually_Abs_filter, rule is_filter.intro)
  apply (auto intro: eventually_conj elim!: eventually_rev_mp)
  done

instance proof
  fix F F' F'' :: "'a filter" and S :: "'a filter set"
  { show "F < F' \<longleftrightarrow> F \<le> F' \<and> \<not> F' \<le> F"
    by (rule less_filter_def) }
  { show "F \<le> F"
    unfolding le_filter_def by simp }
  { assume "F \<le> F'" and "F' \<le> F''" thus "F \<le> F''"
    unfolding le_filter_def by simp }
  { assume "F \<le> F'" and "F' \<le> F" thus "F = F'"
    unfolding le_filter_def filter_eq_iff by fast }
  { show "inf F F' \<le> F" and "inf F F' \<le> F'"
    unfolding le_filter_def eventually_inf by (auto intro: eventually_True) }
  { assume "F \<le> F'" and "F \<le> F''" thus "F \<le> inf F' F''"
    unfolding le_filter_def eventually_inf
    by (auto intro: eventually_mono [OF eventually_conj]) }
  { show "F \<le> sup F F'" and "F' \<le> sup F F'"
    unfolding le_filter_def eventually_sup by simp_all }
  { assume "F \<le> F''" and "F' \<le> F''" thus "sup F F' \<le> F''"
    unfolding le_filter_def eventually_sup by simp }
  { assume "F'' \<in> S" thus "Inf S \<le> F''"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
  { assume "\<And>F'. F' \<in> S \<Longrightarrow> F \<le> F'" thus "F \<le> Inf S"
    unfolding le_filter_def Inf_filter_def eventually_Sup Ball_def by simp }
  { assume "F \<in> S" thus "F \<le> Sup S"
    unfolding le_filter_def eventually_Sup by simp }
  { assume "\<And>F. F \<in> S \<Longrightarrow> F \<le> F'" thus "Sup S \<le> F'"
    unfolding le_filter_def eventually_Sup by simp }
  { show "Inf {} = (top::'a filter)"
    by (auto simp: top_filter_def Inf_filter_def Sup_filter_def)
      (metis (full_types) top_filter_def always_eventually eventually_top) }
  { show "Sup {} = (bot::'a filter)"
    by (auto simp: bot_filter_def Sup_filter_def) }
qed

end

instance filter :: (type) distrib_lattice
proof
  fix F G H :: "'a filter"
  show "sup F (inf G H) = inf (sup F G) (sup F H)"
  proof (rule order.antisym)
    show "inf (sup F G) (sup F H) \<le> sup F (inf G H)" 
      unfolding le_filter_def eventually_sup
    proof safe
      fix P assume 1: "eventually P F" and 2: "eventually P (inf G H)"
      from 2 obtain Q R 
        where QR: "eventually Q G" "eventually R H" "\<And>x. Q x \<Longrightarrow> R x \<Longrightarrow> P x"
        by (auto simp: eventually_inf)
      define Q' where "Q' = (\<lambda>x. Q x \<or> P x)"
      define R' where "R' = (\<lambda>x. R x \<or> P x)"
      from 1 have "eventually Q' F" 
        by (elim eventually_mono) (auto simp: Q'_def)
      moreover from 1 have "eventually R' F" 
        by (elim eventually_mono) (auto simp: R'_def)
      moreover from QR(1) have "eventually Q' G" 
        by (elim eventually_mono) (auto simp: Q'_def)
      moreover from QR(2) have "eventually R' H" 
        by (elim eventually_mono)(auto simp: R'_def)
      moreover from QR have "P x" if "Q' x" "R' x" for x 
        using that by (auto simp: Q'_def R'_def)
      ultimately show "eventually P (inf (sup F G) (sup F H))"
        by (auto simp: eventually_inf eventually_sup)
    qed
  qed (auto intro: inf.coboundedI1 inf.coboundedI2)
qed


lemma filter_leD:
  "F \<le> F' \<Longrightarrow> eventually P F' \<Longrightarrow> eventually P F"
  unfolding le_filter_def by simp

lemma filter_leI:
  "(\<And>P. eventually P F' \<Longrightarrow> eventually P F) \<Longrightarrow> F \<le> F'"
  unfolding le_filter_def by simp

lemma eventually_False:
  "eventually (\<lambda>x. False) F \<longleftrightarrow> F = bot"
  unfolding filter_eq_iff by (auto elim: eventually_rev_mp)

lemma eventually_frequently: "F \<noteq> bot \<Longrightarrow> eventually P F \<Longrightarrow> frequently P F"
  using eventually_conj[of P F "\<lambda>x. \<not> P x"]
  by (auto simp add: frequently_def eventually_False)

lemma eventually_frequentlyE:
  assumes "eventually P F"
  assumes "eventually (\<lambda>x. \<not> P x \<or> Q x) F" "F\<noteq>bot"
  shows "frequently Q F"
proof -
  have "eventually Q F"
    using eventually_conj[OF assms(1,2),simplified] by (auto elim:eventually_mono)
  then show ?thesis using eventually_frequently[OF \<open>F\<noteq>bot\<close>] by auto
qed

lemma eventually_const_iff: "eventually (\<lambda>x. P) F \<longleftrightarrow> P \<or> F = bot"
  by (cases P) (auto simp: eventually_False)

lemma eventually_const[simp]: "F \<noteq> bot \<Longrightarrow> eventually (\<lambda>x. P) F \<longleftrightarrow> P"
  by (simp add: eventually_const_iff)

lemma frequently_const_iff: "frequently (\<lambda>x. P) F \<longleftrightarrow> P \<and> F \<noteq> bot"
  by (simp add: frequently_def eventually_const_iff)

lemma frequently_const[simp]: "F \<noteq> bot \<Longrightarrow> frequently (\<lambda>x. P) F \<longleftrightarrow> P"
  by (simp add: frequently_const_iff)

lemma eventually_happens: "eventually P net \<Longrightarrow> net = bot \<or> (\<exists>x. P x)"
  by (metis frequentlyE eventually_frequently)

lemma eventually_happens':
  assumes "F \<noteq> bot" "eventually P F"
  shows   "\<exists>x. P x"
  using assms eventually_frequently frequentlyE by blast

abbreviation (input) trivial_limit :: "'a filter \<Rightarrow> bool"
  where "trivial_limit F \<equiv> F = bot"

lemma trivial_limit_def: "trivial_limit F \<longleftrightarrow> eventually (\<lambda>x. False) F"
  by (rule eventually_False [symmetric])

lemma False_imp_not_eventually: "(\<forall>x. \<not> P x ) \<Longrightarrow> \<not> trivial_limit net \<Longrightarrow> \<not> eventually (\<lambda>x. P x) net"
  by (simp add: eventually_False)

lemma eventually_Inf: "eventually P (Inf B) \<longleftrightarrow> (\<exists>X\<subseteq>B. finite X \<and> eventually P (Inf X))"
proof -
  let ?F = "\<lambda>P. \<exists>X\<subseteq>B. finite X \<and> eventually P (Inf X)"

  { fix P have "eventually P (Abs_filter ?F) \<longleftrightarrow> ?F P"
    proof (rule eventually_Abs_filter is_filter.intro)+
      show "?F (\<lambda>x. True)"
        by (rule exI[of _ "{}"]) (simp add: le_fun_def)
    next
      fix P Q
      assume "?F P" then guess X ..
      moreover
      assume "?F Q" then guess Y ..
      ultimately show "?F (\<lambda>x. P x \<and> Q x)"
        by (intro exI[of _ "X \<union> Y"])
           (auto simp: Inf_union_distrib eventually_inf)
    next
      fix P Q
      assume "?F P" then guess X ..
      moreover assume "\<forall>x. P x \<longrightarrow> Q x"
      ultimately show "?F Q"
        by (intro exI[of _ X]) (auto elim: eventually_mono)
    qed }
  note eventually_F = this

  have "Inf B = Abs_filter ?F"
  proof (intro antisym Inf_greatest)
    show "Inf B \<le> Abs_filter ?F"
      by (auto simp: le_filter_def eventually_F dest: Inf_superset_mono)
  next
    fix F assume "F \<in> B" then show "Abs_filter ?F \<le> F"
      by (auto simp add: le_filter_def eventually_F intro!: exI[of _ "{F}"])
  qed
  then show ?thesis
    by (simp add: eventually_F)
qed

lemma eventually_INF: "eventually P (\<Sqinter>b\<in>B. F b) \<longleftrightarrow> (\<exists>X\<subseteq>B. finite X \<and> eventually P (\<Sqinter>b\<in>X. F b))"
  unfolding eventually_Inf [of P "F`B"]
  by (metis finite_imageI image_mono finite_subset_image)

lemma Inf_filter_not_bot:
  fixes B :: "'a filter set"
  shows "(\<And>X. X \<subseteq> B \<Longrightarrow> finite X \<Longrightarrow> Inf X \<noteq> bot) \<Longrightarrow> Inf B \<noteq> bot"
  unfolding trivial_limit_def eventually_Inf[of _ B]
    bot_bool_def [symmetric] bot_fun_def [symmetric] bot_unique by simp

lemma INF_filter_not_bot:
  fixes F :: "'i \<Rightarrow> 'a filter"
  shows "(\<And>X. X \<subseteq> B \<Longrightarrow> finite X \<Longrightarrow> (\<Sqinter>b\<in>X. F b) \<noteq> bot) \<Longrightarrow> (\<Sqinter>b\<in>B. F b) \<noteq> bot"
  unfolding trivial_limit_def eventually_INF [of _ _ B]
    bot_bool_def [symmetric] bot_fun_def [symmetric] bot_unique by simp

lemma eventually_Inf_base:
  assumes "B \<noteq> {}" and base: "\<And>F G. F \<in> B \<Longrightarrow> G \<in> B \<Longrightarrow> \<exists>x\<in>B. x \<le> inf F G"
  shows "eventually P (Inf B) \<longleftrightarrow> (\<exists>b\<in>B. eventually P b)"
proof (subst eventually_Inf, safe)
  fix X assume "finite X" "X \<subseteq> B"
  then have "\<exists>b\<in>B. \<forall>x\<in>X. b \<le> x"
  proof induct
    case empty then show ?case
      using \<open>B \<noteq> {}\<close> by auto
  next
    case (insert x X)
    then obtain b where "b \<in> B" "\<And>x. x \<in> X \<Longrightarrow> b \<le> x"
      by auto
    with \<open>insert x X \<subseteq> B\<close> base[of b x] show ?case
      by (auto intro: order_trans)
  qed
  then obtain b where "b \<in> B" "b \<le> Inf X"
    by (auto simp: le_Inf_iff)
  then show "eventually P (Inf X) \<Longrightarrow> Bex B (eventually P)"
    by (intro bexI[of _ b]) (auto simp: le_filter_def)
qed (auto intro!: exI[of _ "{x}" for x])

lemma eventually_INF_base:
  "B \<noteq> {} \<Longrightarrow> (\<And>a b. a \<in> B \<Longrightarrow> b \<in> B \<Longrightarrow> \<exists>x\<in>B. F x \<le> inf (F a) (F b)) \<Longrightarrow>
    eventually P (\<Sqinter>b\<in>B. F b) \<longleftrightarrow> (\<exists>b\<in>B. eventually P (F b))"
  by (subst eventually_Inf_base) auto

lemma eventually_INF1: "i \<in> I \<Longrightarrow> eventually P (F i) \<Longrightarrow> eventually P (\<Sqinter>i\<in>I. F i)"
  using filter_leD[OF INF_lower] .

lemma eventually_INF_mono:
  assumes *: "\<forall>\<^sub>F x in \<Sqinter>i\<in>I. F i. P x"
  assumes T1: "\<And>Q R P. (\<And>x. Q x \<and> R x \<longrightarrow> P x) \<Longrightarrow> (\<And>x. T Q x \<Longrightarrow> T R x \<Longrightarrow> T P x)"
  assumes T2: "\<And>P. (\<And>x. P x) \<Longrightarrow> (\<And>x. T P x)"
  assumes **: "\<And>i P. i \<in> I \<Longrightarrow> \<forall>\<^sub>F x in F i. P x \<Longrightarrow> \<forall>\<^sub>F x in F' i. T P x"
  shows "\<forall>\<^sub>F x in \<Sqinter>i\<in>I. F' i. T P x"
proof -
  from * obtain X where X: "finite X" "X \<subseteq> I" "\<forall>\<^sub>F x in \<Sqinter>i\<in>X. F i. P x"
    unfolding eventually_INF[of _ _ I] by auto
  then have "eventually (T P) (INFIMUM X F')"
    apply (induction X arbitrary: P)
    apply (auto simp: eventually_inf T2)
    subgoal for x S P Q R
      apply (intro exI[of _ "T Q"])
      apply (auto intro!: **) []
      apply (intro exI[of _ "T R"])
      apply (auto intro: T1) []
      done
    done
  with X show "\<forall>\<^sub>F x in \<Sqinter>i\<in>I. F' i. T P x"
    by (subst eventually_INF) auto
qed


subsubsection \<open>Map function for filters\<close>

definition filtermap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> 'b filter"
  where "filtermap f F = Abs_filter (\<lambda>P. eventually (\<lambda>x. P (f x)) F)"

lemma eventually_filtermap:
  "eventually P (filtermap f F) = eventually (\<lambda>x. P (f x)) F"
  unfolding filtermap_def
  apply (rule eventually_Abs_filter)
  apply (rule is_filter.intro)
  apply (auto elim!: eventually_rev_mp)
  done

lemma filtermap_ident: "filtermap (\<lambda>x. x) F = F"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_filtermap:
  "filtermap f (filtermap g F) = filtermap (\<lambda>x. f (g x)) F"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_mono: "F \<le> F' \<Longrightarrow> filtermap f F \<le> filtermap f F'"
  unfolding le_filter_def eventually_filtermap by simp

lemma filtermap_bot [simp]: "filtermap f bot = bot"
  by (simp add: filter_eq_iff eventually_filtermap)

lemma filtermap_sup: "filtermap f (sup F1 F2) = sup (filtermap f F1) (filtermap f F2)"
  by (auto simp: filter_eq_iff eventually_filtermap eventually_sup)

lemma filtermap_inf: "filtermap f (inf F1 F2) \<le> inf (filtermap f F1) (filtermap f F2)"
  by (auto simp: le_filter_def eventually_filtermap eventually_inf)

lemma filtermap_INF: "filtermap f (\<Sqinter>b\<in>B. F b) \<le> (\<Sqinter>b\<in>B. filtermap f (F b))"
proof -
  { fix X :: "'c set" assume "finite X"
    then have "filtermap f (INFIMUM X F) \<le> (\<Sqinter>b\<in>X. filtermap f (F b))"
    proof induct
      case (insert x X)
      have "filtermap f (\<Sqinter>a\<in>insert x X. F a) \<le> inf (filtermap f (F x)) (filtermap f (\<Sqinter>a\<in>X. F a))"
        by (rule order_trans[OF _ filtermap_inf]) simp
      also have "\<dots> \<le> inf (filtermap f (F x)) (\<Sqinter>a\<in>X. filtermap f (F a))"
        by (intro inf_mono insert order_refl)
      finally show ?case
        by simp
    qed simp }
  then show ?thesis
    unfolding le_filter_def eventually_filtermap
    by (subst (1 2) eventually_INF) auto
qed


subsubsection \<open>Contravariant map function for filters\<close>

definition filtercomap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b filter \<Rightarrow> 'a filter" where
  "filtercomap f F = Abs_filter (\<lambda>P. \<exists>Q. eventually Q F \<and> (\<forall>x. Q (f x) \<longrightarrow> P x))"

lemma eventually_filtercomap:
  "eventually P (filtercomap f F) \<longleftrightarrow> (\<exists>Q. eventually Q F \<and> (\<forall>x. Q (f x) \<longrightarrow> P x))"
  unfolding filtercomap_def
proof (intro eventually_Abs_filter, unfold_locales, goal_cases)
  case 1
  show ?case by (auto intro!: exI[of _ "\<lambda>_. True"])
next
  case (2 P Q)
  from 2(1) guess P' by (elim exE conjE) note P' = this
  from 2(2) guess Q' by (elim exE conjE) note Q' = this
  show ?case
    by (rule exI[of _ "\<lambda>x. P' x \<and> Q' x"])
       (insert P' Q', auto intro!: eventually_conj)
next
  case (3 P Q)
  thus ?case by blast
qed

lemma filtercomap_ident: "filtercomap (\<lambda>x. x) F = F"
  by (auto simp: filter_eq_iff eventually_filtercomap elim!: eventually_mono)

lemma filtercomap_filtercomap: "filtercomap f (filtercomap g F) = filtercomap (\<lambda>x. g (f x)) F"
  unfolding filter_eq_iff by (auto simp: eventually_filtercomap)
  
lemma filtercomap_mono: "F \<le> F' \<Longrightarrow> filtercomap f F \<le> filtercomap f F'"
  by (auto simp: eventually_filtercomap le_filter_def)

lemma filtercomap_bot [simp]: "filtercomap f bot = bot"
  by (auto simp: filter_eq_iff eventually_filtercomap)

lemma filtercomap_top [simp]: "filtercomap f top = top"
  by (auto simp: filter_eq_iff eventually_filtercomap)

lemma filtercomap_inf: "filtercomap f (inf F1 F2) = inf (filtercomap f F1) (filtercomap f F2)"
  unfolding filter_eq_iff
proof safe
  fix P
  assume "eventually P (filtercomap f (F1 \<sqinter> F2))"
  then obtain Q R S where *:
    "eventually Q F1" "eventually R F2" "\<And>x. Q x \<Longrightarrow> R x \<Longrightarrow> S x" "\<And>x. S (f x) \<Longrightarrow> P x"
    unfolding eventually_filtercomap eventually_inf by blast
  from * have "eventually (\<lambda>x. Q (f x)) (filtercomap f F1)" 
              "eventually (\<lambda>x. R (f x)) (filtercomap f F2)"
    by (auto simp: eventually_filtercomap)
  with * show "eventually P (filtercomap f F1 \<sqinter> filtercomap f F2)"
    unfolding eventually_inf by blast
next
  fix P
  assume "eventually P (inf (filtercomap f F1) (filtercomap f F2))"
  then obtain Q Q' R R' where *:
    "eventually Q F1" "eventually R F2" "\<And>x. Q (f x) \<Longrightarrow> Q' x" "\<And>x. R (f x) \<Longrightarrow> R' x" 
    "\<And>x. Q' x \<Longrightarrow> R' x \<Longrightarrow> P x"
    unfolding eventually_filtercomap eventually_inf by blast
  from * have "eventually (\<lambda>x. Q x \<and> R x) (F1 \<sqinter> F2)" by (auto simp: eventually_inf)
  with * show "eventually P (filtercomap f (F1 \<sqinter> F2))"
    by (auto simp: eventually_filtercomap)
qed

lemma filtercomap_sup: "filtercomap f (sup F1 F2) \<ge> sup (filtercomap f F1) (filtercomap f F2)"
  unfolding le_filter_def
proof safe
  fix P
  assume "eventually P (filtercomap f (sup F1 F2))"
  thus "eventually P (sup (filtercomap f F1) (filtercomap f F2))"
    by (auto simp: filter_eq_iff eventually_filtercomap eventually_sup)
qed

lemma filtercomap_INF: "filtercomap f (\<Sqinter>b\<in>B. F b) = (\<Sqinter>b\<in>B. filtercomap f (F b))"
proof -
  have *: "filtercomap f (\<Sqinter>b\<in>B. F b) = (\<Sqinter>b\<in>B. filtercomap f (F b))" if "finite B" for B
    using that by induction (simp_all add: filtercomap_inf)
  show ?thesis unfolding filter_eq_iff
  proof
    fix P
    have "eventually P (\<Sqinter>b\<in>B. filtercomap f (F b)) \<longleftrightarrow> 
            (\<exists>X. (X \<subseteq> B \<and> finite X) \<and> eventually P (\<Sqinter>b\<in>X. filtercomap f (F b)))"
      by (subst eventually_INF) blast
    also have "\<dots> \<longleftrightarrow> (\<exists>X. (X \<subseteq> B \<and> finite X) \<and> eventually P (filtercomap f (\<Sqinter>b\<in>X. F b)))"
      by (rule ex_cong) (simp add: *)
    also have "\<dots> \<longleftrightarrow> eventually P (filtercomap f (INFIMUM B F))"
      unfolding eventually_filtercomap by (subst eventually_INF) blast
    finally show "eventually P (filtercomap f (INFIMUM B F)) = 
                    eventually P (\<Sqinter>b\<in>B. filtercomap f (F b))" ..
  qed
qed

lemma filtercomap_SUP_finite: 
  "finite B \<Longrightarrow> filtercomap f (\<Squnion>b\<in>B. F b) \<ge> (\<Squnion>b\<in>B. filtercomap f (F b))"
  by (induction B rule: finite_induct)
     (auto intro: order_trans[OF _ order_trans[OF _ filtercomap_sup]] filtercomap_mono)
     
lemma eventually_filtercomapI [intro]:
  assumes "eventually P F"
  shows   "eventually (\<lambda>x. P (f x)) (filtercomap f F)"
  using assms by (auto simp: eventually_filtercomap)

lemma filtermap_filtercomap: "filtermap f (filtercomap f F) \<le> F"
  by (auto simp: le_filter_def eventually_filtermap eventually_filtercomap)
    
lemma filtercomap_filtermap: "filtercomap f (filtermap f F) \<ge> F"
  unfolding le_filter_def eventually_filtermap eventually_filtercomap
  by (auto elim!: eventually_mono)


subsubsection \<open>Standard filters\<close>

definition principal :: "'a set \<Rightarrow> 'a filter" where
  "principal S = Abs_filter (\<lambda>P. \<forall>x\<in>S. P x)"

lemma eventually_principal: "eventually P (principal S) \<longleftrightarrow> (\<forall>x\<in>S. P x)"
  unfolding principal_def
  by (rule eventually_Abs_filter, rule is_filter.intro) auto

lemma eventually_inf_principal: "eventually P (inf F (principal s)) \<longleftrightarrow> eventually (\<lambda>x. x \<in> s \<longrightarrow> P x) F"
  unfolding eventually_inf eventually_principal by (auto elim: eventually_mono)

lemma principal_UNIV[simp]: "principal UNIV = top"
  by (auto simp: filter_eq_iff eventually_principal)

lemma principal_empty[simp]: "principal {} = bot"
  by (auto simp: filter_eq_iff eventually_principal)

lemma principal_eq_bot_iff: "principal X = bot \<longleftrightarrow> X = {}"
  by (auto simp add: filter_eq_iff eventually_principal)

lemma principal_le_iff[iff]: "principal A \<le> principal B \<longleftrightarrow> A \<subseteq> B"
  by (auto simp: le_filter_def eventually_principal)

lemma le_principal: "F \<le> principal A \<longleftrightarrow> eventually (\<lambda>x. x \<in> A) F"
  unfolding le_filter_def eventually_principal
  apply safe
  apply (erule_tac x="\<lambda>x. x \<in> A" in allE)
  apply (auto elim: eventually_mono)
  done

lemma principal_inject[iff]: "principal A = principal B \<longleftrightarrow> A = B"
  unfolding eq_iff by simp

lemma sup_principal[simp]: "sup (principal A) (principal B) = principal (A \<union> B)"
  unfolding filter_eq_iff eventually_sup eventually_principal by auto

lemma inf_principal[simp]: "inf (principal A) (principal B) = principal (A \<inter> B)"
  unfolding filter_eq_iff eventually_inf eventually_principal
  by (auto intro: exI[of _ "\<lambda>x. x \<in> A"] exI[of _ "\<lambda>x. x \<in> B"])

lemma SUP_principal[simp]: "(\<Squnion>i\<in>I. principal (A i)) = principal (\<Union>i\<in>I. A i)"
  unfolding filter_eq_iff eventually_Sup by (auto simp: eventually_principal)

lemma INF_principal_finite: "finite X \<Longrightarrow> (\<Sqinter>x\<in>X. principal (f x)) = principal (\<Inter>x\<in>X. f x)"
  by (induct X rule: finite_induct) auto

lemma filtermap_principal[simp]: "filtermap f (principal A) = principal (f ` A)"
  unfolding filter_eq_iff eventually_filtermap eventually_principal by simp
    
lemma filtercomap_principal[simp]: "filtercomap f (principal A) = principal (f -` A)"
  unfolding filter_eq_iff eventually_filtercomap eventually_principal by fast

subsubsection \<open>Order filters\<close>

definition at_top :: "('a::order) filter"
  where "at_top = (\<Sqinter>k. principal {k ..})"

lemma at_top_sub: "at_top = (\<Sqinter>k\<in>{c::'a::linorder..}. principal {k ..})"
  by (auto intro!: INF_eq max.cobounded1 max.cobounded2 simp: at_top_def)

lemma eventually_at_top_linorder: "eventually P at_top \<longleftrightarrow> (\<exists>N::'a::linorder. \<forall>n\<ge>N. P n)"
  unfolding at_top_def
  by (subst eventually_INF_base) (auto simp: eventually_principal intro: max.cobounded1 max.cobounded2)

lemma eventually_filtercomap_at_top_linorder: 
  "eventually P (filtercomap f at_top) \<longleftrightarrow> (\<exists>N::'a::linorder. \<forall>x. f x \<ge> N \<longrightarrow> P x)"
  by (auto simp: eventually_filtercomap eventually_at_top_linorder)

lemma eventually_at_top_linorderI:
  fixes c::"'a::linorder"
  assumes "\<And>x. c \<le> x \<Longrightarrow> P x"
  shows "eventually P at_top"
  using assms by (auto simp: eventually_at_top_linorder)

lemma eventually_ge_at_top [simp]:
  "eventually (\<lambda>x. (c::_::linorder) \<le> x) at_top"
  unfolding eventually_at_top_linorder by auto

lemma eventually_at_top_dense: "eventually P at_top \<longleftrightarrow> (\<exists>N::'a::{no_top, linorder}. \<forall>n>N. P n)"
proof -
  have "eventually P (\<Sqinter>k. principal {k <..}) \<longleftrightarrow> (\<exists>N::'a. \<forall>n>N. P n)"
    by (subst eventually_INF_base) (auto simp: eventually_principal intro: max.cobounded1 max.cobounded2)
  also have "(\<Sqinter>k. principal {k::'a <..}) = at_top"
    unfolding at_top_def
    by (intro INF_eq) (auto intro: less_imp_le simp: Ici_subset_Ioi_iff gt_ex)
  finally show ?thesis .
qed
  
lemma eventually_filtercomap_at_top_dense: 
  "eventually P (filtercomap f at_top) \<longleftrightarrow> (\<exists>N::'a::{no_top, linorder}. \<forall>x. f x > N \<longrightarrow> P x)"
  by (auto simp: eventually_filtercomap eventually_at_top_dense)

lemma eventually_at_top_not_equal [simp]: "eventually (\<lambda>x::'a::{no_top, linorder}. x \<noteq> c) at_top"
  unfolding eventually_at_top_dense by auto

lemma eventually_gt_at_top [simp]: "eventually (\<lambda>x. (c::_::{no_top, linorder}) < x) at_top"
  unfolding eventually_at_top_dense by auto

lemma eventually_all_ge_at_top:
  assumes "eventually P (at_top :: ('a :: linorder) filter)"
  shows   "eventually (\<lambda>x. \<forall>y\<ge>x. P y) at_top"
proof -
  from assms obtain x where "\<And>y. y \<ge> x \<Longrightarrow> P y" by (auto simp: eventually_at_top_linorder)
  hence "\<forall>z\<ge>y. P z" if "y \<ge> x" for y using that by simp
  thus ?thesis by (auto simp: eventually_at_top_linorder)
qed

definition at_bot :: "('a::order) filter"
  where "at_bot = (\<Sqinter>k. principal {.. k})"

lemma at_bot_sub: "at_bot = (\<Sqinter>k\<in>{.. c::'a::linorder}. principal {.. k})"
  by (auto intro!: INF_eq min.cobounded1 min.cobounded2 simp: at_bot_def)

lemma eventually_at_bot_linorder:
  fixes P :: "'a::linorder \<Rightarrow> bool" shows "eventually P at_bot \<longleftrightarrow> (\<exists>N. \<forall>n\<le>N. P n)"
  unfolding at_bot_def
  by (subst eventually_INF_base) (auto simp: eventually_principal intro: min.cobounded1 min.cobounded2)

lemma eventually_filtercomap_at_bot_linorder: 
  "eventually P (filtercomap f at_bot) \<longleftrightarrow> (\<exists>N::'a::linorder. \<forall>x. f x \<le> N \<longrightarrow> P x)"
  by (auto simp: eventually_filtercomap eventually_at_bot_linorder)

lemma eventually_le_at_bot [simp]:
  "eventually (\<lambda>x. x \<le> (c::_::linorder)) at_bot"
  unfolding eventually_at_bot_linorder by auto

lemma eventually_at_bot_dense: "eventually P at_bot \<longleftrightarrow> (\<exists>N::'a::{no_bot, linorder}. \<forall>n<N. P n)"
proof -
  have "eventually P (\<Sqinter>k. principal {..< k}) \<longleftrightarrow> (\<exists>N::'a. \<forall>n<N. P n)"
    by (subst eventually_INF_base) (auto simp: eventually_principal intro: min.cobounded1 min.cobounded2)
  also have "(\<Sqinter>k. principal {..< k::'a}) = at_bot"
    unfolding at_bot_def
    by (intro INF_eq) (auto intro: less_imp_le simp: Iic_subset_Iio_iff lt_ex)
  finally show ?thesis .
qed

lemma eventually_filtercomap_at_bot_dense: 
  "eventually P (filtercomap f at_bot) \<longleftrightarrow> (\<exists>N::'a::{no_bot, linorder}. \<forall>x. f x < N \<longrightarrow> P x)"
  by (auto simp: eventually_filtercomap eventually_at_bot_dense)

lemma eventually_at_bot_not_equal [simp]: "eventually (\<lambda>x::'a::{no_bot, linorder}. x \<noteq> c) at_bot"
  unfolding eventually_at_bot_dense by auto

lemma eventually_gt_at_bot [simp]:
  "eventually (\<lambda>x. x < (c::_::unbounded_dense_linorder)) at_bot"
  unfolding eventually_at_bot_dense by auto

lemma trivial_limit_at_bot_linorder [simp]: "\<not> trivial_limit (at_bot ::('a::linorder) filter)"
  unfolding trivial_limit_def
  by (metis eventually_at_bot_linorder order_refl)

lemma trivial_limit_at_top_linorder [simp]: "\<not> trivial_limit (at_top ::('a::linorder) filter)"
  unfolding trivial_limit_def
  by (metis eventually_at_top_linorder order_refl)

subsection \<open>Sequentially\<close>

abbreviation sequentially :: "nat filter"
  where "sequentially \<equiv> at_top"

lemma eventually_sequentially:
  "eventually P sequentially \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. P n)"
  by (rule eventually_at_top_linorder)

lemma sequentially_bot [simp, intro]: "sequentially \<noteq> bot"
  unfolding filter_eq_iff eventually_sequentially by auto

lemmas trivial_limit_sequentially = sequentially_bot

lemma eventually_False_sequentially [simp]:
  "\<not> eventually (\<lambda>n. False) sequentially"
  by (simp add: eventually_False)

lemma le_sequentially:
  "F \<le> sequentially \<longleftrightarrow> (\<forall>N. eventually (\<lambda>n. N \<le> n) F)"
  by (simp add: at_top_def le_INF_iff le_principal)

lemma eventually_sequentiallyI [intro?]:
  assumes "\<And>x. c \<le> x \<Longrightarrow> P x"
  shows "eventually P sequentially"
using assms by (auto simp: eventually_sequentially)

lemma eventually_sequentially_Suc [simp]: "eventually (\<lambda>i. P (Suc i)) sequentially \<longleftrightarrow> eventually P sequentially"
  unfolding eventually_sequentially by (metis Suc_le_D Suc_le_mono le_Suc_eq)

lemma eventually_sequentially_seg [simp]: "eventually (\<lambda>n. P (n + k)) sequentially \<longleftrightarrow> eventually P sequentially"
  using eventually_sequentially_Suc[of "\<lambda>n. P (n + k)" for k] by (induction k) auto


subsection \<open>The cofinite filter\<close>

definition "cofinite = Abs_filter (\<lambda>P. finite {x. \<not> P x})"

abbreviation Inf_many :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "\<exists>\<^sub>\<infinity>" 10)
  where "Inf_many P \<equiv> frequently P cofinite"

abbreviation Alm_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"  (binder "\<forall>\<^sub>\<infinity>" 10)
  where "Alm_all P \<equiv> eventually P cofinite"

notation (ASCII)
  Inf_many  (binder "INFM " 10) and
  Alm_all  (binder "MOST " 10)

lemma eventually_cofinite: "eventually P cofinite \<longleftrightarrow> finite {x. \<not> P x}"
  unfolding cofinite_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool" assume "finite {x. \<not> P x}" "finite {x. \<not> Q x}"
  from finite_UnI[OF this] show "finite {x. \<not> (P x \<and> Q x)}"
    by (rule rev_finite_subset) auto
next
  fix P Q :: "'a \<Rightarrow> bool" assume P: "finite {x. \<not> P x}" and *: "\<forall>x. P x \<longrightarrow> Q x"
  from * show "finite {x. \<not> Q x}"
    by (intro finite_subset[OF _ P]) auto
qed simp

lemma frequently_cofinite: "frequently P cofinite \<longleftrightarrow> \<not> finite {x. P x}"
  by (simp add: frequently_def eventually_cofinite)

lemma cofinite_bot[simp]: "cofinite = (bot::'a filter) \<longleftrightarrow> finite (UNIV :: 'a set)"
  unfolding trivial_limit_def eventually_cofinite by simp

lemma cofinite_eq_sequentially: "cofinite = sequentially"
  unfolding filter_eq_iff eventually_sequentially eventually_cofinite
proof safe
  fix P :: "nat \<Rightarrow> bool" assume [simp]: "finite {x. \<not> P x}"
  show "\<exists>N. \<forall>n\<ge>N. P n"
  proof cases
    assume "{x. \<not> P x} \<noteq> {}" then show ?thesis
      by (intro exI[of _ "Suc (Max {x. \<not> P x})"]) (auto simp: Suc_le_eq)
  qed auto
next
  fix P :: "nat \<Rightarrow> bool" and N :: nat assume "\<forall>n\<ge>N. P n"
  then have "{x. \<not> P x} \<subseteq> {..< N}"
    by (auto simp: not_le)
  then show "finite {x. \<not> P x}"
    by (blast intro: finite_subset)
qed

subsubsection \<open>Product of filters\<close>

lemma filtermap_sequentually_ne_bot: "filtermap f sequentially \<noteq> bot"
  by (auto simp add: filter_eq_iff eventually_filtermap eventually_sequentially)

definition prod_filter :: "'a filter \<Rightarrow> 'b filter \<Rightarrow> ('a \<times> 'b) filter" (infixr "\<times>\<^sub>F" 80) where
  "prod_filter F G =
    (\<Sqinter>(P, Q)\<in>{(P, Q). eventually P F \<and> eventually Q G}. principal {(x, y). P x \<and> Q y})"

lemma eventually_prod_filter: "eventually P (F \<times>\<^sub>F G) \<longleftrightarrow>
  (\<exists>Pf Pg. eventually Pf F \<and> eventually Pg G \<and> (\<forall>x y. Pf x \<longrightarrow> Pg y \<longrightarrow> P (x, y)))"
  unfolding prod_filter_def
proof (subst eventually_INF_base, goal_cases)
  case 2
  moreover have "eventually Pf F \<Longrightarrow> eventually Qf F \<Longrightarrow> eventually Pg G \<Longrightarrow> eventually Qg G \<Longrightarrow>
    \<exists>P Q. eventually P F \<and> eventually Q G \<and>
      Collect P \<times> Collect Q \<subseteq> Collect Pf \<times> Collect Pg \<inter> Collect Qf \<times> Collect Qg" for Pf Pg Qf Qg
    by (intro conjI exI[of _ "inf Pf Qf"] exI[of _ "inf Pg Qg"])
       (auto simp: inf_fun_def eventually_conj)
  ultimately show ?case
    by auto
qed (auto simp: eventually_principal intro: eventually_True)

lemma eventually_prod1:
  assumes "B \<noteq> bot"
  shows "(\<forall>\<^sub>F (x, y) in A \<times>\<^sub>F B. P x) \<longleftrightarrow> (\<forall>\<^sub>F x in A. P x)"
  unfolding eventually_prod_filter
proof safe
  fix R Q
  assume *: "\<forall>\<^sub>F x in A. R x" "\<forall>\<^sub>F x in B. Q x" "\<forall>x y. R x \<longrightarrow> Q y \<longrightarrow> P x"
  with \<open>B \<noteq> bot\<close> obtain y where "Q y" by (auto dest: eventually_happens)
  with * show "eventually P A"
    by (force elim: eventually_mono)
next
  assume "eventually P A"
  then show "\<exists>Pf Pg. eventually Pf A \<and> eventually Pg B \<and> (\<forall>x y. Pf x \<longrightarrow> Pg y \<longrightarrow> P x)"
    by (intro exI[of _ P] exI[of _ "\<lambda>x. True"]) auto
qed

lemma eventually_prod2:
  assumes "A \<noteq> bot"
  shows "(\<forall>\<^sub>F (x, y) in A \<times>\<^sub>F B. P y) \<longleftrightarrow> (\<forall>\<^sub>F y in B. P y)"
  unfolding eventually_prod_filter
proof safe
  fix R Q
  assume *: "\<forall>\<^sub>F x in A. R x" "\<forall>\<^sub>F x in B. Q x" "\<forall>x y. R x \<longrightarrow> Q y \<longrightarrow> P y"
  with \<open>A \<noteq> bot\<close> obtain x where "R x" by (auto dest: eventually_happens)
  with * show "eventually P B"
    by (force elim: eventually_mono)
next
  assume "eventually P B"
  then show "\<exists>Pf Pg. eventually Pf A \<and> eventually Pg B \<and> (\<forall>x y. Pf x \<longrightarrow> Pg y \<longrightarrow> P y)"
    by (intro exI[of _ P] exI[of _ "\<lambda>x. True"]) auto
qed

lemma INF_filter_bot_base:
  fixes F :: "'a \<Rightarrow> 'b filter"
  assumes *: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<exists>k\<in>I. F k \<le> F i \<sqinter> F j"
  shows "(\<Sqinter>i\<in>I. F i) = bot \<longleftrightarrow> (\<exists>i\<in>I. F i = bot)"
proof (cases "\<exists>i\<in>I. F i = bot")
  case True
  then have "(\<Sqinter>i\<in>I. F i) \<le> bot"
    by (auto intro: INF_lower2)
  with True show ?thesis
    by (auto simp: bot_unique)
next
  case False
  moreover have "(\<Sqinter>i\<in>I. F i) \<noteq> bot"
  proof (cases "I = {}")
    case True
    then show ?thesis
      by (auto simp add: filter_eq_iff)
  next
    case False': False
    show ?thesis
    proof (rule INF_filter_not_bot)
      fix J
      assume "finite J" "J \<subseteq> I"
      then have "\<exists>k\<in>I. F k \<le> (\<Sqinter>i\<in>J. F i)"
      proof (induct J)
        case empty
        then show ?case
          using \<open>I \<noteq> {}\<close> by auto
      next
        case (insert i J)
        then obtain k where "k \<in> I" "F k \<le> (\<Sqinter>i\<in>J. F i)" by auto
        with insert *[of i k] show ?case
          by auto
      qed
      with False show "(\<Sqinter>i\<in>J. F i) \<noteq> \<bottom>"
        by (auto simp: bot_unique)
    qed
  qed
  ultimately show ?thesis
    by auto
qed

lemma Collect_empty_eq_bot: "Collect P = {} \<longleftrightarrow> P = \<bottom>"
  by auto

lemma prod_filter_eq_bot: "A \<times>\<^sub>F B = bot \<longleftrightarrow> A = bot \<or> B = bot"
  unfolding prod_filter_def
proof (subst INF_filter_bot_base; clarsimp simp: principal_eq_bot_iff Collect_empty_eq_bot bot_fun_def simp del: Collect_empty_eq)
  fix A1 A2 B1 B2 assume "\<forall>\<^sub>F x in A. A1 x" "\<forall>\<^sub>F x in A. A2 x" "\<forall>\<^sub>F x in B. B1 x" "\<forall>\<^sub>F x in B. B2 x"
  then show "\<exists>x. eventually x A \<and> (\<exists>y. eventually y B \<and> Collect x \<times> Collect y \<subseteq> Collect A1 \<times> Collect B1 \<and> Collect x \<times> Collect y \<subseteq> Collect A2 \<times> Collect B2)"
    by (intro exI[of _ "\<lambda>x. A1 x \<and> A2 x"] exI[of _ "\<lambda>x. B1 x \<and> B2 x"] conjI)
       (auto simp: eventually_conj_iff)
next
  show "(\<exists>x. eventually x A \<and> (\<exists>y. eventually y B \<and> (x = (\<lambda>x. False) \<or> y = (\<lambda>x. False)))) = (A = \<bottom> \<or> B = \<bottom>)"
    by (auto simp: trivial_limit_def intro: eventually_True)
qed

lemma prod_filter_mono: "F \<le> F' \<Longrightarrow> G \<le> G' \<Longrightarrow> F \<times>\<^sub>F G \<le> F' \<times>\<^sub>F G'"
  by (auto simp: le_filter_def eventually_prod_filter)

lemma prod_filter_mono_iff:
  assumes nAB: "A \<noteq> bot" "B \<noteq> bot"
  shows "A \<times>\<^sub>F B \<le> C \<times>\<^sub>F D \<longleftrightarrow> A \<le> C \<and> B \<le> D"
proof safe
  assume *: "A \<times>\<^sub>F B \<le> C \<times>\<^sub>F D"
  with assms have "A \<times>\<^sub>F B \<noteq> bot"
    by (auto simp: bot_unique prod_filter_eq_bot)
  with * have "C \<times>\<^sub>F D \<noteq> bot"
    by (auto simp: bot_unique)
  then have nCD: "C \<noteq> bot" "D \<noteq> bot"
    by (auto simp: prod_filter_eq_bot)

  show "A \<le> C"
  proof (rule filter_leI)
    fix P assume "eventually P C" with *[THEN filter_leD, of "\<lambda>(x, y). P x"] show "eventually P A"
      using nAB nCD by (simp add: eventually_prod1 eventually_prod2)
  qed

  show "B \<le> D"
  proof (rule filter_leI)
    fix P assume "eventually P D" with *[THEN filter_leD, of "\<lambda>(x, y). P y"] show "eventually P B"
      using nAB nCD by (simp add: eventually_prod1 eventually_prod2)
  qed
qed (intro prod_filter_mono)

lemma eventually_prod_same: "eventually P (F \<times>\<^sub>F F) \<longleftrightarrow>
    (\<exists>Q. eventually Q F \<and> (\<forall>x y. Q x \<longrightarrow> Q y \<longrightarrow> P (x, y)))"
  unfolding eventually_prod_filter
  apply safe
  apply (rule_tac x="inf Pf Pg" in exI)
  apply (auto simp: inf_fun_def intro!: eventually_conj)
  done

lemma eventually_prod_sequentially:
  "eventually P (sequentially \<times>\<^sub>F sequentially) \<longleftrightarrow> (\<exists>N. \<forall>m \<ge> N. \<forall>n \<ge> N. P (n, m))"
  unfolding eventually_prod_same eventually_sequentially by auto

lemma principal_prod_principal: "principal A \<times>\<^sub>F principal B = principal (A \<times> B)"
  apply (simp add: filter_eq_iff eventually_prod_filter eventually_principal)
  apply safe
  apply blast
  apply (intro conjI exI[of _ "\<lambda>x. x \<in> A"] exI[of _ "\<lambda>x. x \<in> B"])
  apply auto
  done

lemma prod_filter_INF:
  assumes "I \<noteq> {}" "J \<noteq> {}"
  shows "(\<Sqinter>i\<in>I. A i) \<times>\<^sub>F (\<Sqinter>j\<in>J. B j) = (\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. A i \<times>\<^sub>F B j)"
proof (safe intro!: antisym INF_greatest)
  from \<open>I \<noteq> {}\<close> obtain i where "i \<in> I" by auto
  from \<open>J \<noteq> {}\<close> obtain j where "j \<in> J" by auto

  show "(\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. A i \<times>\<^sub>F B j) \<le> (\<Sqinter>i\<in>I. A i) \<times>\<^sub>F (\<Sqinter>j\<in>J. B j)"
    unfolding prod_filter_def
  proof (safe intro!: INF_greatest)
    fix P Q assume P: "\<forall>\<^sub>F x in \<Sqinter>i\<in>I. A i. P x" and Q: "\<forall>\<^sub>F x in \<Sqinter>j\<in>J. B j. Q x"
    let ?X = "(\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. \<Sqinter>(P, Q)\<in>{(P, Q). (\<forall>\<^sub>F x in A i. P x) \<and> (\<forall>\<^sub>F x in B j. Q x)}. principal {(x, y). P x \<and> Q y})"
    have "?X \<le> principal {x. P (fst x)} \<sqinter> principal {x. Q (snd x)}"
    proof (intro inf_greatest)
      have "?X \<le> (\<Sqinter>i\<in>I. \<Sqinter>P\<in>{P. eventually P (A i)}. principal {x. P (fst x)})"
        by (auto intro!: INF_greatest INF_lower2[of j] INF_lower2 \<open>j\<in>J\<close> INF_lower2[of "(_, \<lambda>x. True)"])
      also have "\<dots> \<le> principal {x. P (fst x)}"
        unfolding le_principal
      proof (rule eventually_INF_mono[OF P])
        fix i P assume "i \<in> I" "eventually P (A i)"
        then show "\<forall>\<^sub>F x in \<Sqinter>P\<in>{P. eventually P (A i)}. principal {x. P (fst x)}. x \<in> {x. P (fst x)}"
          unfolding le_principal[symmetric] by (auto intro!: INF_lower)
      qed auto
      finally show "?X \<le> principal {x. P (fst x)}" .

      have "?X \<le> (\<Sqinter>i\<in>J. \<Sqinter>P\<in>{P. eventually P (B i)}. principal {x. P (snd x)})"
        by (auto intro!: INF_greatest INF_lower2[of i] INF_lower2 \<open>i\<in>I\<close> INF_lower2[of "(\<lambda>x. True, _)"])
      also have "\<dots> \<le> principal {x. Q (snd x)}"
        unfolding le_principal
      proof (rule eventually_INF_mono[OF Q])
        fix j Q assume "j \<in> J" "eventually Q (B j)"
        then show "\<forall>\<^sub>F x in \<Sqinter>P\<in>{P. eventually P (B j)}. principal {x. P (snd x)}. x \<in> {x. Q (snd x)}"
          unfolding le_principal[symmetric] by (auto intro!: INF_lower)
      qed auto
      finally show "?X \<le> principal {x. Q (snd x)}" .
    qed
    also have "\<dots> = principal {(x, y). P x \<and> Q y}"
      by auto
    finally show "?X \<le> principal {(x, y). P x \<and> Q y}" .
  qed
qed (intro prod_filter_mono INF_lower)

lemma filtermap_Pair: "filtermap (\<lambda>x. (f x, g x)) F \<le> filtermap f F \<times>\<^sub>F filtermap g F"
  by (simp add: le_filter_def eventually_filtermap eventually_prod_filter)
     (auto elim: eventually_elim2)

lemma eventually_prodI: "eventually P F \<Longrightarrow> eventually Q G \<Longrightarrow> eventually (\<lambda>x. P (fst x) \<and> Q (snd x)) (F \<times>\<^sub>F G)"
  unfolding prod_filter_def
  by (intro eventually_INF1[of "(P, Q)"]) (auto simp: eventually_principal)

lemma prod_filter_INF1: "I \<noteq> {} \<Longrightarrow> (\<Sqinter>i\<in>I. A i) \<times>\<^sub>F B = (\<Sqinter>i\<in>I. A i \<times>\<^sub>F B)"
  using prod_filter_INF[of I "{B}" A "\<lambda>x. x"] by simp

lemma prod_filter_INF2: "J \<noteq> {} \<Longrightarrow> A \<times>\<^sub>F (\<Sqinter>i\<in>J. B i) = (\<Sqinter>i\<in>J. A \<times>\<^sub>F B i)"
  using prod_filter_INF[of "{A}" J "\<lambda>x. x" B] by simp

subsection \<open>Limits\<close>

definition filterlim :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b filter \<Rightarrow> 'a filter \<Rightarrow> bool" where
  "filterlim f F2 F1 \<longleftrightarrow> filtermap f F1 \<le> F2"

syntax
  "_LIM" :: "pttrns \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(3LIM (_)/ (_)./ (_) :> (_))" [1000, 10, 0, 10] 10)

translations
  "LIM x F1. f :> F2" == "CONST filterlim (\<lambda>x. f) F2 F1"

lemma filterlim_top [simp]: "filterlim f top F"
  by (simp add: filterlim_def)

lemma filterlim_iff:
  "(LIM x F1. f x :> F2) \<longleftrightarrow> (\<forall>P. eventually P F2 \<longrightarrow> eventually (\<lambda>x. P (f x)) F1)"
  unfolding filterlim_def le_filter_def eventually_filtermap ..

lemma filterlim_compose:
  "filterlim g F3 F2 \<Longrightarrow> filterlim f F2 F1 \<Longrightarrow> filterlim (\<lambda>x. g (f x)) F3 F1"
  unfolding filterlim_def filtermap_filtermap[symmetric] by (metis filtermap_mono order_trans)

lemma filterlim_mono:
  "filterlim f F2 F1 \<Longrightarrow> F2 \<le> F2' \<Longrightarrow> F1' \<le> F1 \<Longrightarrow> filterlim f F2' F1'"
  unfolding filterlim_def by (metis filtermap_mono order_trans)

lemma filterlim_ident: "LIM x F. x :> F"
  by (simp add: filterlim_def filtermap_ident)

lemma filterlim_cong:
  "F1 = F1' \<Longrightarrow> F2 = F2' \<Longrightarrow> eventually (\<lambda>x. f x = g x) F2 \<Longrightarrow> filterlim f F1 F2 = filterlim g F1' F2'"
  by (auto simp: filterlim_def le_filter_def eventually_filtermap elim: eventually_elim2)

lemma filterlim_mono_eventually:
  assumes "filterlim f F G" and ord: "F \<le> F'" "G' \<le> G"
  assumes eq: "eventually (\<lambda>x. f x = f' x) G'"
  shows "filterlim f' F' G'"
  apply (rule filterlim_cong[OF refl refl eq, THEN iffD1])
  apply (rule filterlim_mono[OF _ ord])
  apply fact
  done

lemma filtermap_mono_strong: "inj f \<Longrightarrow> filtermap f F \<le> filtermap f G \<longleftrightarrow> F \<le> G"
  apply (auto intro!: filtermap_mono) []
  apply (auto simp: le_filter_def eventually_filtermap)
  apply (erule_tac x="\<lambda>x. P (inv f x)" in allE)
  apply auto
  done

lemma filtermap_eq_strong: "inj f \<Longrightarrow> filtermap f F = filtermap f G \<longleftrightarrow> F = G"
  by (simp add: filtermap_mono_strong eq_iff)

lemma filtermap_fun_inverse:
  assumes g: "filterlim g F G"
  assumes f: "filterlim f G F"
  assumes ev: "eventually (\<lambda>x. f (g x) = x) G"
  shows "filtermap f F = G"
proof (rule antisym)
  show "filtermap f F \<le> G"
    using f unfolding filterlim_def .
  have "G = filtermap f (filtermap g G)"
    using ev by (auto elim: eventually_elim2 simp: filter_eq_iff eventually_filtermap)
  also have "\<dots> \<le> filtermap f F"
    using g by (intro filtermap_mono) (simp add: filterlim_def)
  finally show "G \<le> filtermap f F" .
qed

lemma filterlim_principal:
  "(LIM x F. f x :> principal S) \<longleftrightarrow> (eventually (\<lambda>x. f x \<in> S) F)"
  unfolding filterlim_def eventually_filtermap le_principal ..

lemma filterlim_inf:
  "(LIM x F1. f x :> inf F2 F3) \<longleftrightarrow> ((LIM x F1. f x :> F2) \<and> (LIM x F1. f x :> F3))"
  unfolding filterlim_def by simp

lemma filterlim_INF:
  "(LIM x F. f x :> (\<Sqinter>b\<in>B. G b)) \<longleftrightarrow> (\<forall>b\<in>B. LIM x F. f x :> G b)"
  unfolding filterlim_def le_INF_iff ..

lemma filterlim_INF_INF:
  "(\<And>m. m \<in> J \<Longrightarrow> \<exists>i\<in>I. filtermap f (F i) \<le> G m) \<Longrightarrow> LIM x (\<Sqinter>i\<in>I. F i). f x :> (\<Sqinter>j\<in>J. G j)"
  unfolding filterlim_def by (rule order_trans[OF filtermap_INF INF_mono])

lemma filterlim_base:
  "(\<And>m x. m \<in> J \<Longrightarrow> i m \<in> I) \<Longrightarrow> (\<And>m x. m \<in> J \<Longrightarrow> x \<in> F (i m) \<Longrightarrow> f x \<in> G m) \<Longrightarrow>
    LIM x (\<Sqinter>i\<in>I. principal (F i)). f x :> (\<Sqinter>j\<in>J. principal (G j))"
  by (force intro!: filterlim_INF_INF simp: image_subset_iff)

lemma filterlim_base_iff:
  assumes "I \<noteq> {}" and chain: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> F i \<subseteq> F j \<or> F j \<subseteq> F i"
  shows "(LIM x (\<Sqinter>i\<in>I. principal (F i)). f x :> \<Sqinter>j\<in>J. principal (G j)) \<longleftrightarrow>
    (\<forall>j\<in>J. \<exists>i\<in>I. \<forall>x\<in>F i. f x \<in> G j)"
  unfolding filterlim_INF filterlim_principal
proof (subst eventually_INF_base)
  fix i j assume "i \<in> I" "j \<in> I"
  with chain[OF this] show "\<exists>x\<in>I. principal (F x) \<le> inf (principal (F i)) (principal (F j))"
    by auto
qed (auto simp: eventually_principal \<open>I \<noteq> {}\<close>)

lemma filterlim_filtermap: "filterlim f F1 (filtermap g F2) = filterlim (\<lambda>x. f (g x)) F1 F2"
  unfolding filterlim_def filtermap_filtermap ..

lemma filterlim_sup:
  "filterlim f F F1 \<Longrightarrow> filterlim f F F2 \<Longrightarrow> filterlim f F (sup F1 F2)"
  unfolding filterlim_def filtermap_sup by auto

lemma filterlim_sequentially_Suc:
  "(LIM x sequentially. f (Suc x) :> F) \<longleftrightarrow> (LIM x sequentially. f x :> F)"
  unfolding filterlim_iff by (subst eventually_sequentially_Suc) simp

lemma filterlim_Suc: "filterlim Suc sequentially sequentially"
  by (simp add: filterlim_iff eventually_sequentially)

lemma filterlim_If:
  "LIM x inf F (principal {x. P x}). f x :> G \<Longrightarrow>
    LIM x inf F (principal {x. \<not> P x}). g x :> G \<Longrightarrow>
    LIM x F. if P x then f x else g x :> G"
  unfolding filterlim_iff eventually_inf_principal by (auto simp: eventually_conj_iff)

lemma filterlim_Pair:
  "LIM x F. f x :> G \<Longrightarrow> LIM x F. g x :> H \<Longrightarrow> LIM x F. (f x, g x) :> G \<times>\<^sub>F H"
  unfolding filterlim_def
  by (rule order_trans[OF filtermap_Pair prod_filter_mono])

subsection \<open>Limits to @{const at_top} and @{const at_bot}\<close>

lemma filterlim_at_top:
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. Z \<le> f x) F)"
  by (auto simp: filterlim_iff eventually_at_top_linorder elim!: eventually_mono)

lemma filterlim_at_top_mono:
  "LIM x F. f x :> at_top \<Longrightarrow> eventually (\<lambda>x. f x \<le> (g x::'a::linorder)) F \<Longrightarrow>
    LIM x F. g x :> at_top"
  by (auto simp: filterlim_at_top elim: eventually_elim2 intro: order_trans)

lemma filterlim_at_top_dense:
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. Z < f x) F)"
  by (metis eventually_mono[of _ F] eventually_gt_at_top order_less_imp_le
            filterlim_at_top[of f F] filterlim_iff[of f at_top F])

lemma filterlim_at_top_ge:
  fixes f :: "'a \<Rightarrow> ('b::linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z\<ge>c. eventually (\<lambda>x. Z \<le> f x) F)"
  unfolding at_top_sub[of c] filterlim_INF by (auto simp add: filterlim_principal)

lemma filterlim_at_top_at_top:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes mono: "\<And>x y. Q x \<Longrightarrow> Q y \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  assumes bij: "\<And>x. P x \<Longrightarrow> f (g x) = x" "\<And>x. P x \<Longrightarrow> Q (g x)"
  assumes Q: "eventually Q at_top"
  assumes P: "eventually P at_top"
  shows "filterlim f at_top at_top"
proof -
  from P obtain x where x: "\<And>y. x \<le> y \<Longrightarrow> P y"
    unfolding eventually_at_top_linorder by auto
  show ?thesis
  proof (intro filterlim_at_top_ge[THEN iffD2] allI impI)
    fix z assume "x \<le> z"
    with x have "P z" by auto
    have "eventually (\<lambda>x. g z \<le> x) at_top"
      by (rule eventually_ge_at_top)
    with Q show "eventually (\<lambda>x. z \<le> f x) at_top"
      by eventually_elim (metis mono bij \<open>P z\<close>)
  qed
qed

lemma filterlim_at_top_gt:
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_top) \<longleftrightarrow> (\<forall>Z>c. eventually (\<lambda>x. Z \<le> f x) F)"
  by (metis filterlim_at_top order_less_le_trans gt_ex filterlim_at_top_ge)

lemma filterlim_at_bot:
  fixes f :: "'a \<Rightarrow> ('b::linorder)"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x \<le> Z) F)"
  by (auto simp: filterlim_iff eventually_at_bot_linorder elim!: eventually_mono)

lemma filterlim_at_bot_dense:
  fixes f :: "'a \<Rightarrow> ('b::{dense_linorder, no_bot})"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x < Z) F)"
proof (auto simp add: filterlim_at_bot[of f F])
  fix Z :: 'b
  from lt_ex [of Z] obtain Z' where 1: "Z' < Z" ..
  assume "\<forall>Z. eventually (\<lambda>x. f x \<le> Z) F"
  hence "eventually (\<lambda>x. f x \<le> Z') F" by auto
  thus "eventually (\<lambda>x. f x < Z) F"
    apply (rule eventually_mono)
    using 1 by auto
  next
    fix Z :: 'b
    show "\<forall>Z. eventually (\<lambda>x. f x < Z) F \<Longrightarrow> eventually (\<lambda>x. f x \<le> Z) F"
      by (drule spec [of _ Z], erule eventually_mono, auto simp add: less_imp_le)
qed

lemma filterlim_at_bot_le:
  fixes f :: "'a \<Rightarrow> ('b::linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z\<le>c. eventually (\<lambda>x. Z \<ge> f x) F)"
  unfolding filterlim_at_bot
proof safe
  fix Z assume *: "\<forall>Z\<le>c. eventually (\<lambda>x. Z \<ge> f x) F"
  with *[THEN spec, of "min Z c"] show "eventually (\<lambda>x. Z \<ge> f x) F"
    by (auto elim!: eventually_mono)
qed simp

lemma filterlim_at_bot_lt:
  fixes f :: "'a \<Rightarrow> ('b::unbounded_dense_linorder)" and c :: "'b"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z<c. eventually (\<lambda>x. Z \<ge> f x) F)"
  by (metis filterlim_at_bot filterlim_at_bot_le lt_ex order_le_less_trans)
    
lemma filterlim_filtercomap [intro]: "filterlim f F (filtercomap f F)"
  unfolding filterlim_def by (rule filtermap_filtercomap)


subsection \<open>Setup @{typ "'a filter"} for lifting and transfer\<close>

lemma filtermap_id [simp, id_simps]: "filtermap id = id"
by(simp add: fun_eq_iff id_def filtermap_ident)

lemma filtermap_id' [simp]: "filtermap (\<lambda>x. x) = (\<lambda>F. F)"
using filtermap_id unfolding id_def .

context includes lifting_syntax
begin

definition map_filter_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "map_filter_on X f F = Abs_filter (\<lambda>P. eventually (\<lambda>x. P (f x) \<and> x \<in> X) F)"

lemma is_filter_map_filter_on:
  "is_filter (\<lambda>P. \<forall>\<^sub>F x in F. P (f x) \<and> x \<in> X) \<longleftrightarrow> eventually (\<lambda>x. x \<in> X) F"
proof(rule iffI; unfold_locales)
  show "\<forall>\<^sub>F x in F. True \<and> x \<in> X" if "eventually (\<lambda>x. x \<in> X) F" using that by simp
  show "\<forall>\<^sub>F x in F. (P (f x) \<and> Q (f x)) \<and> x \<in> X" if "\<forall>\<^sub>F x in F. P (f x) \<and> x \<in> X" "\<forall>\<^sub>F x in F. Q (f x) \<and> x \<in> X" for P Q
    using eventually_conj[OF that] by(auto simp add: conj_ac cong: conj_cong)
  show "\<forall>\<^sub>F x in F. Q (f x) \<and> x \<in> X" if "\<forall>x. P x \<longrightarrow> Q x" "\<forall>\<^sub>F x in F. P (f x) \<and> x \<in> X" for P Q
    using that(2) by(rule eventually_mono)(use that(1) in auto)
  show "eventually (\<lambda>x. x \<in> X) F" if "is_filter (\<lambda>P. \<forall>\<^sub>F x in F. P (f x) \<and> x \<in> X)"
    using is_filter.True[OF that] by simp
qed

lemma eventually_map_filter_on: "eventually P (map_filter_on X f F) = (\<forall>\<^sub>F x in F. P (f x) \<and> x \<in> X)"
  if "eventually (\<lambda>x. x \<in> X) F"
  by(simp add: is_filter_map_filter_on map_filter_on_def eventually_Abs_filter that)

lemma map_filter_on_UNIV: "map_filter_on UNIV = filtermap"
  by(simp add: map_filter_on_def filtermap_def fun_eq_iff)

lemma map_filter_on_comp: "map_filter_on X f (map_filter_on Y g F) = map_filter_on Y (f \<circ> g) F"
  if "g ` Y \<subseteq> X" and "eventually (\<lambda>x. x \<in> Y) F"
  unfolding map_filter_on_def using that(1)
  by(auto simp add: eventually_Abs_filter that(2) is_filter_map_filter_on intro!: arg_cong[where f=Abs_filter] arg_cong2[where f=eventually])

inductive rel_filter :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a filter \<Rightarrow> 'b filter \<Rightarrow> bool" for R F G where
  "rel_filter R F G" if "eventually (case_prod R) Z" "map_filter_on {(x, y). R x y} fst Z = F" "map_filter_on {(x, y). R x y} snd Z = G"

lemma rel_filter_eq [relator_eq]: "rel_filter (=) = (=)"
proof(intro ext iffI)+
  show "F = G" if "rel_filter (=) F G" for F G using that
    by cases(clarsimp simp add: filter_eq_iff eventually_map_filter_on split_def cong: rev_conj_cong)
  show "rel_filter (=) F G" if "F = G" for F G unfolding \<open>F = G\<close>
  proof
    let ?Z = "map_filter_on UNIV (\<lambda>x. (x, x)) G"
    have [simp]: "range (\<lambda>x. (x, x)) \<subseteq> {(x, y). x = y}" by auto
    show "map_filter_on {(x, y). x = y} fst ?Z = G" and "map_filter_on {(x, y). x = y} snd ?Z = G"
      by(simp_all add: map_filter_on_comp)(simp_all add: map_filter_on_UNIV o_def)
    show "\<forall>\<^sub>F (x, y) in ?Z. x = y" by(simp add: eventually_map_filter_on)
  qed
qed

lemma rel_filter_mono [relator_mono]: "rel_filter A \<le> rel_filter B" if le: "A \<le> B"
proof(clarify elim!: rel_filter.cases)
  show "rel_filter B (map_filter_on {(x, y). A x y} fst Z) (map_filter_on {(x, y). A x y} snd Z)"
    (is "rel_filter _ ?X ?Y") if "\<forall>\<^sub>F (x, y) in Z. A x y" for Z
  proof
    let ?Z = "map_filter_on {(x, y). A x y} id Z"
    show "\<forall>\<^sub>F (x, y) in ?Z. B x y" using le that
      by(simp add: eventually_map_filter_on le_fun_def split_def conj_commute cong: conj_cong)
    have [simp]: "{(x, y). A x y} \<subseteq> {(x, y). B x y}" using le by auto
    show "map_filter_on {(x, y). B x y} fst ?Z = ?X" "map_filter_on {(x, y). B x y} snd ?Z = ?Y"
      using le that by(simp_all add: le_fun_def map_filter_on_comp)
  qed
qed

lemma rel_filter_conversep: "rel_filter A\<inverse>\<inverse> = (rel_filter A)\<inverse>\<inverse>"
proof(safe intro!: ext elim!: rel_filter.cases)
  show *: "rel_filter A (map_filter_on {(x, y). A\<inverse>\<inverse> x y} snd Z) (map_filter_on {(x, y). A\<inverse>\<inverse> x y} fst Z)"
    (is "rel_filter _ ?X ?Y") if "\<forall>\<^sub>F (x, y) in Z. A\<inverse>\<inverse> x y" for A Z
  proof
    let ?Z = "map_filter_on {(x, y). A y x} prod.swap Z"
    show "\<forall>\<^sub>F (x, y) in ?Z. A x y" using that by(simp add: eventually_map_filter_on)
    have [simp]: "prod.swap ` {(x, y). A y x} \<subseteq> {(x, y). A x y}" by auto
    show "map_filter_on {(x, y). A x y} fst ?Z = ?X" "map_filter_on {(x, y). A x y} snd ?Z = ?Y"
      using that by(simp_all add: map_filter_on_comp o_def)
  qed
  show "rel_filter A\<inverse>\<inverse> (map_filter_on {(x, y). A x y} snd Z) (map_filter_on {(x, y). A x y} fst Z)"
    if "\<forall>\<^sub>F (x, y) in Z. A x y" for Z using *[of "A\<inverse>\<inverse>" Z] that by simp
qed

lemma rel_filter_distr [relator_distr]:
  "rel_filter A OO rel_filter B = rel_filter (A OO B)"
proof(safe intro!: ext elim!: rel_filter.cases)
  let ?AB = "{(x, y). (A OO B) x y}"
  show "(rel_filter A OO rel_filter B)
     (map_filter_on {(x, y). (A OO B) x y} fst Z) (map_filter_on {(x, y). (A OO B) x y} snd Z)"
    (is "(_ OO _) ?F ?H") if "\<forall>\<^sub>F (x, y) in Z. (A OO B) x y" for Z
  proof
    let ?G = "map_filter_on ?AB (\<lambda>(x, y). SOME z. A x z \<and> B z y) Z"
    show "rel_filter A ?F ?G"
    proof
      let ?Z = "map_filter_on ?AB (\<lambda>(x, y). (x, SOME z. A x z \<and> B z y)) Z"
      show "\<forall>\<^sub>F (x, y) in ?Z. A x y" using that
        by(auto simp add: eventually_map_filter_on split_def elim!: eventually_mono intro: someI2)
      have [simp]: "(\<lambda>p. (fst p, SOME z. A (fst p) z \<and> B z (snd p))) ` {p. (A OO B) (fst p) (snd p)} \<subseteq> {p. A (fst p) (snd p)}" by(auto intro: someI2)
      show "map_filter_on {(x, y). A x y} fst ?Z = ?F" "map_filter_on {(x, y). A x y} snd ?Z = ?G"
        using that by(simp_all add: map_filter_on_comp split_def o_def)
    qed
    show "rel_filter B ?G ?H"
    proof
      let ?Z = "map_filter_on ?AB (\<lambda>(x, y). (SOME z. A x z \<and> B z y, y)) Z"
      show "\<forall>\<^sub>F (x, y) in ?Z. B x y" using that
        by(auto simp add: eventually_map_filter_on split_def elim!: eventually_mono intro: someI2)
      have [simp]: "(\<lambda>p. (SOME z. A (fst p) z \<and> B z (snd p), snd p)) ` {p. (A OO B) (fst p) (snd p)} \<subseteq> {p. B (fst p) (snd p)}" by(auto intro: someI2)
      show "map_filter_on {(x, y). B x y} fst ?Z = ?G" "map_filter_on {(x, y). B x y} snd ?Z = ?H"
        using that by(simp_all add: map_filter_on_comp split_def o_def)
    qed
  qed

  fix F G
  assume F: "\<forall>\<^sub>F (x, y) in F. A x y" and G: "\<forall>\<^sub>F (x, y) in G. B x y"
    and eq: "map_filter_on {(x, y). B x y} fst G = map_filter_on {(x, y). A x y} snd F" (is "?Y2 = ?Y1")
  let ?X = "map_filter_on {(x, y). A x y} fst F"
    and ?Z = "(map_filter_on {(x, y). B x y} snd G)"
  have step: "\<exists>P'\<le>P. \<exists>Q' \<le> Q. eventually P' F \<and> eventually Q' G \<and> {y. \<exists>x. P' (x, y)} = {y. \<exists>z. Q' (y, z)}"
    if P: "eventually P F" and Q: "eventually Q G" for P Q
  proof -
    let ?P = "\<lambda>(x, y). P (x, y) \<and> A x y" and ?Q = "\<lambda>(y, z). Q (y, z) \<and> B y z"
    define P' where "P' \<equiv> \<lambda>(x, y). ?P (x, y) \<and> (\<exists>z. ?Q (y, z))"
    define Q' where "Q' \<equiv> \<lambda>(y, z). ?Q (y, z) \<and> (\<exists>x. ?P (x, y))"
    have "P' \<le> P" "Q' \<le> Q" "{y. \<exists>x. P' (x, y)} = {y. \<exists>z. Q' (y, z)}"
      by(auto simp add: P'_def Q'_def)
    moreover
    from P Q F G have P': "eventually ?P F" and Q': "eventually ?Q G" 
      by(simp_all add: eventually_conj_iff split_def)
    from P' F have "\<forall>\<^sub>F y in ?Y1. \<exists>x. P (x, y) \<and> A x y"
      by(auto simp add: eventually_map_filter_on elim!: eventually_mono)
    from this[folded eq] obtain Q'' where Q'': "eventually Q'' G"
      and Q''P: "{y. \<exists>z. Q'' (y, z)} \<subseteq> {y. \<exists>x. ?P (x, y)}"
      using G by(fastforce simp add: eventually_map_filter_on)
    have "eventually (inf Q'' ?Q) G" using Q'' Q' by(auto intro: eventually_conj simp add: inf_fun_def)
    then have "eventually Q' G" using Q''P  by(auto elim!: eventually_mono simp add: Q'_def)
    moreover
    from Q' G have "\<forall>\<^sub>F y in ?Y2. \<exists>z. Q (y, z) \<and> B y z"
      by(auto simp add: eventually_map_filter_on elim!: eventually_mono)
    from this[unfolded eq] obtain P'' where P'': "eventually P'' F"
      and P''Q: "{y. \<exists>x. P'' (x, y)} \<subseteq> {y. \<exists>z. ?Q (y, z)}"
      using F by(fastforce simp add: eventually_map_filter_on)
    have "eventually (inf P'' ?P) F" using P'' P' by(auto intro: eventually_conj simp add: inf_fun_def)
    then have "eventually P' F" using P''Q  by(auto elim!: eventually_mono simp add: P'_def)
    ultimately show ?thesis by blast
  qed

  show "rel_filter (A OO B) ?X ?Z"
  proof
    let ?Y = "\<lambda>Y. \<exists>X Z. eventually X ?X \<and> eventually Z ?Z \<and> (\<lambda>(x, z). X x \<and> Z z \<and> (A OO B) x z) \<le> Y"
    have Y: "is_filter ?Y"
    proof
      show "?Y (\<lambda>_. True)" by(auto simp add: le_fun_def intro: eventually_True)
      show "?Y (\<lambda>x. P x \<and> Q x)" if "?Y P" "?Y Q" for P Q using that
        apply clarify
        apply(intro exI conjI; (elim eventually_rev_mp; fold imp_conjL; intro always_eventually allI; rule imp_refl)?)
        apply auto
        done
      show "?Y Q" if "?Y P" "\<forall>x. P x \<longrightarrow> Q x" for P Q using that by blast
    qed
    define Y where "Y = Abs_filter ?Y"
    have eventually_Y: "eventually P Y \<longleftrightarrow> ?Y P" for P
      using eventually_Abs_filter[OF Y, of P] by(simp add: Y_def)
    show YY: "\<forall>\<^sub>F (x, y) in Y. (A OO B) x y" using F G
      by(auto simp add: eventually_Y eventually_map_filter_on eventually_conj_iff intro!: eventually_True)
    have "?Y (\<lambda>(x, z). P x \<and> (A OO B) x z) \<longleftrightarrow> (\<forall>\<^sub>F (x, y) in F. P x \<and> A x y)" (is "?lhs = ?rhs") for P
    proof
      show ?lhs if ?rhs using G F that
        by(auto 4 3 intro: exI[where x="\<lambda>_. True"] simp add: eventually_map_filter_on split_def)
      assume ?lhs
      then obtain X Z where "\<forall>\<^sub>F (x, y) in F. X x \<and> A x y"
        and "\<forall>\<^sub>F (x, y) in G. Z y \<and> B x y"
        and "(\<lambda>(x, z). X x \<and> Z z \<and> (A OO B) x z) \<le> (\<lambda>(x, z). P x \<and> (A OO B) x z)"
        using F G by(auto simp add: eventually_map_filter_on split_def)
      from step[OF this(1, 2)] this(3)
      show ?rhs by(clarsimp elim!: eventually_rev_mp simp add: le_fun_def)(fastforce intro: always_eventually)
    qed
    then show "map_filter_on ?AB fst Y = ?X"
      by(simp add: filter_eq_iff YY eventually_map_filter_on)(simp add: eventually_Y eventually_map_filter_on F G; simp add: split_def)

    have "?Y (\<lambda>(x, z). P z \<and> (A OO B) x z) \<longleftrightarrow> (\<forall>\<^sub>F (x, y) in G. P y \<and> B x y)" (is "?lhs = ?rhs") for P
    proof
      show ?lhs if ?rhs using G F that
        by(auto 4 3 intro: exI[where x="\<lambda>_. True"] simp add: eventually_map_filter_on split_def)
      assume ?lhs
      then obtain X Z where "\<forall>\<^sub>F (x, y) in F. X x \<and> A x y"
        and "\<forall>\<^sub>F (x, y) in G. Z y \<and> B x y"
        and "(\<lambda>(x, z). X x \<and> Z z \<and> (A OO B) x z) \<le> (\<lambda>(x, z). P z \<and> (A OO B) x z)"
        using F G by(auto simp add: eventually_map_filter_on split_def)
      from step[OF this(1, 2)] this(3)
      show ?rhs by(clarsimp elim!: eventually_rev_mp simp add: le_fun_def)(fastforce intro: always_eventually)
    qed
    then show "map_filter_on ?AB snd Y = ?Z"
      by(simp add: filter_eq_iff YY eventually_map_filter_on)(simp add: eventually_Y eventually_map_filter_on F G; simp add: split_def)
  qed
qed

lemma filtermap_parametric: "((A ===> B) ===> rel_filter A ===> rel_filter B) filtermap filtermap"
proof(intro rel_funI; erule rel_filter.cases; hypsubst)
  fix f g Z
  assume fg: "(A ===> B) f g" and Z: "\<forall>\<^sub>F (x, y) in Z. A x y"
  have "rel_filter B (map_filter_on {(x, y). A x y} (f \<circ> fst) Z) (map_filter_on {(x, y). A x y} (g \<circ> snd) Z)"
    (is "rel_filter _ ?F ?G")
  proof
    let ?Z = "map_filter_on {(x, y). A x y} (map_prod f g) Z"
    show "\<forall>\<^sub>F (x, y) in ?Z. B x y" using fg Z
      by(auto simp add: eventually_map_filter_on split_def elim!: eventually_mono rel_funD)
    have [simp]: "map_prod f g ` {p. A (fst p) (snd p)} \<subseteq> {p. B (fst p) (snd p)}"
      using fg by(auto dest: rel_funD)
    show "map_filter_on {(x, y). B x y} fst ?Z = ?F" "map_filter_on {(x, y). B x y} snd ?Z = ?G"
      using Z by(auto simp add: map_filter_on_comp split_def)
  qed
  thus "rel_filter B (filtermap f (map_filter_on {(x, y). A x y} fst Z)) (filtermap g (map_filter_on {(x, y). A x y} snd Z))"
    using Z by(simp add: map_filter_on_UNIV[symmetric] map_filter_on_comp)
qed

lemma rel_filter_Grp: "rel_filter (Grp UNIV f) = Grp UNIV (filtermap f)"
proof((intro antisym predicate2I; (elim GrpE; hypsubst)?), rule GrpI[OF _ UNIV_I])
  fix F G
  assume "rel_filter (Grp UNIV f) F G"
  hence "rel_filter (=) (filtermap f F) (filtermap id G)"
    by(rule filtermap_parametric[THEN rel_funD, THEN rel_funD, rotated])(simp add: Grp_def rel_fun_def)
  thus "filtermap f F = G" by(simp add: rel_filter_eq)
next
  fix F :: "'a filter"
  have "rel_filter (=) F F" by(simp add: rel_filter_eq)
  hence "rel_filter (Grp UNIV f) (filtermap id F) (filtermap f F)"
    by(rule filtermap_parametric[THEN rel_funD, THEN rel_funD, rotated])(simp add: Grp_def rel_fun_def)
  thus "rel_filter (Grp UNIV f) F (filtermap f F)" by simp
qed

lemma Quotient_filter [quot_map]:
  "Quotient R Abs Rep T \<Longrightarrow> Quotient (rel_filter R) (filtermap Abs) (filtermap Rep) (rel_filter T)"
  unfolding Quotient_alt_def5 rel_filter_eq[symmetric] rel_filter_Grp[symmetric]
  by(simp add: rel_filter_distr[symmetric] rel_filter_conversep[symmetric] rel_filter_mono)

lemma left_total_rel_filter [transfer_rule]: "left_total A \<Longrightarrow> left_total (rel_filter A)"
unfolding left_total_alt_def rel_filter_eq[symmetric] rel_filter_conversep[symmetric] rel_filter_distr
by(rule rel_filter_mono)

lemma right_total_rel_filter [transfer_rule]: "right_total A \<Longrightarrow> right_total (rel_filter A)"
using left_total_rel_filter[of "A\<inverse>\<inverse>"] by(simp add: rel_filter_conversep)

lemma bi_total_rel_filter [transfer_rule]: "bi_total A \<Longrightarrow> bi_total (rel_filter A)"
unfolding bi_total_alt_def by(simp add: left_total_rel_filter right_total_rel_filter)

lemma left_unique_rel_filter [transfer_rule]: "left_unique A \<Longrightarrow> left_unique (rel_filter A)"
unfolding left_unique_alt_def rel_filter_eq[symmetric] rel_filter_conversep[symmetric] rel_filter_distr
by(rule rel_filter_mono)

lemma right_unique_rel_filter [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (rel_filter A)"
using left_unique_rel_filter[of "A\<inverse>\<inverse>"] by(simp add: rel_filter_conversep)

lemma bi_unique_rel_filter [transfer_rule]: "bi_unique A \<Longrightarrow> bi_unique (rel_filter A)"
by(simp add: bi_unique_alt_def left_unique_rel_filter right_unique_rel_filter)

lemma eventually_parametric [transfer_rule]:
  "((A ===> (=)) ===> rel_filter A ===> (=)) eventually eventually"
by(auto 4 4 intro!: rel_funI elim!: rel_filter.cases simp add: eventually_map_filter_on dest: rel_funD intro: always_eventually elim!: eventually_rev_mp)

lemma frequently_parametric [transfer_rule]: "((A ===> (=)) ===> rel_filter A ===> (=)) frequently frequently"
  unfolding frequently_def[abs_def] by transfer_prover

lemma is_filter_parametric_aux:
  assumes "is_filter F"
  assumes [transfer_rule]: "bi_total A" "bi_unique A"
  and [transfer_rule]: "((A ===> (=)) ===> (=)) F G"
  shows "is_filter G"
proof -
  interpret is_filter F by fact
  show ?thesis
  proof
    have "F (\<lambda>_. True) = G (\<lambda>x. True)" by transfer_prover
    thus "G (\<lambda>x. True)" by(simp add: True)
  next
    fix P' Q'
    assume "G P'" "G Q'"
    moreover
    from bi_total_fun[OF \<open>bi_unique A\<close> bi_total_eq, unfolded bi_total_def]
    obtain P Q where [transfer_rule]: "(A ===> (=)) P P'" "(A ===> (=)) Q Q'" by blast
    have "F P = G P'" "F Q = G Q'" by transfer_prover+
    ultimately have "F (\<lambda>x. P x \<and> Q x)" by(simp add: conj)
    moreover have "F (\<lambda>x. P x \<and> Q x) = G (\<lambda>x. P' x \<and> Q' x)" by transfer_prover
    ultimately show "G (\<lambda>x. P' x \<and> Q' x)" by simp
  next
    fix P' Q'
    assume "\<forall>x. P' x \<longrightarrow> Q' x" "G P'"
    moreover
    from bi_total_fun[OF \<open>bi_unique A\<close> bi_total_eq, unfolded bi_total_def]
    obtain P Q where [transfer_rule]: "(A ===> (=)) P P'" "(A ===> (=)) Q Q'" by blast
    have "F P = G P'" by transfer_prover
    moreover have "(\<forall>x. P x \<longrightarrow> Q x) \<longleftrightarrow> (\<forall>x. P' x \<longrightarrow> Q' x)" by transfer_prover
    ultimately have "F Q" by(simp add: mono)
    moreover have "F Q = G Q'" by transfer_prover
    ultimately show "G Q'" by simp
  qed
qed

lemma is_filter_parametric [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique A \<rbrakk>
  \<Longrightarrow> (((A ===> (=)) ===> (=)) ===> (=)) is_filter is_filter"
apply(rule rel_funI)
apply(rule iffI)
 apply(erule (3) is_filter_parametric_aux)
apply(erule is_filter_parametric_aux[where A="conversep A"])
apply (simp_all add: rel_fun_def)
apply metis
done

lemma top_filter_parametric [transfer_rule]: "rel_filter A top top" if "bi_total A"
proof
  let ?Z = "principal {(x, y). A x y}"
  show "\<forall>\<^sub>F (x, y) in ?Z. A x y" by(simp add: eventually_principal)
  show "map_filter_on {(x, y). A x y} fst ?Z = top" "map_filter_on {(x, y). A x y} snd ?Z = top"
    using that by(auto simp add: filter_eq_iff eventually_map_filter_on eventually_principal bi_total_def)
qed

lemma bot_filter_parametric [transfer_rule]: "rel_filter A bot bot"
proof
  show "\<forall>\<^sub>F (x, y) in bot. A x y" by simp
  show "map_filter_on {(x, y). A x y} fst bot = bot" "map_filter_on {(x, y). A x y} snd bot = bot"
    by(simp_all add: filter_eq_iff eventually_map_filter_on)
qed

lemma principal_parametric [transfer_rule]: "(rel_set A ===> rel_filter A) principal principal"
proof(rule rel_funI rel_filter.intros)+
  fix S S'
  assume *: "rel_set A S S'"
  define SS' where "SS' = S \<times> S' \<inter> {(x, y). A x y}"
  have SS': "SS' \<subseteq> {(x, y). A x y}" and [simp]: "S = fst ` SS'" "S' = snd ` SS'"
    using * by(auto 4 3 dest: rel_setD1 rel_setD2 intro: rev_image_eqI simp add: SS'_def)
  let ?Z = "principal SS'"
  show "\<forall>\<^sub>F (x, y) in ?Z. A x y" using SS' by(auto simp add: eventually_principal)
  then show "map_filter_on {(x, y). A x y} fst ?Z = principal S"
    and "map_filter_on {(x, y). A x y} snd ?Z = principal S'"
    by(auto simp add: filter_eq_iff eventually_map_filter_on eventually_principal)
qed

lemma sup_filter_parametric [transfer_rule]:
  "(rel_filter A ===> rel_filter A ===> rel_filter A) sup sup"
proof(intro rel_funI; elim rel_filter.cases; hypsubst)
  show "rel_filter A
    (map_filter_on {(x, y). A x y} fst FG \<squnion> map_filter_on {(x, y). A x y} fst FG')
    (map_filter_on {(x, y). A x y} snd FG \<squnion> map_filter_on {(x, y). A x y} snd FG')"
    (is "rel_filter _ (sup ?F ?G) (sup ?F' ?G')")
    if "\<forall>\<^sub>F (x, y) in FG. A x y" "\<forall>\<^sub>F (x, y) in FG'. A x y" for FG FG'
  proof
    let ?Z = "sup FG FG'"
    show "\<forall>\<^sub>F (x, y) in ?Z. A x y" by(simp add: eventually_sup that)
    then show "map_filter_on {(x, y). A x y} fst ?Z = sup ?F ?G" 
      and "map_filter_on {(x, y). A x y} snd ?Z = sup ?F' ?G'"
      by(simp_all add: filter_eq_iff eventually_map_filter_on eventually_sup)
  qed
qed

lemma Sup_filter_parametric [transfer_rule]: "(rel_set (rel_filter A) ===> rel_filter A) Sup Sup"
proof(rule rel_funI)
  fix S S'
  define SS' where "SS' = S \<times> S' \<inter> {(F, G). rel_filter A F G}"
  assume "rel_set (rel_filter A) S S'"
  then have SS': "SS' \<subseteq> {(F, G). rel_filter A F G}" and [simp]: "S = fst ` SS'" "S' = snd ` SS'"
    by(auto 4 3 dest: rel_setD1 rel_setD2 intro: rev_image_eqI simp add: SS'_def)
  from SS' obtain Z where Z: "\<And>F G. (F, G) \<in> SS' \<Longrightarrow>
    (\<forall>\<^sub>F (x, y) in Z F G. A x y) \<and>
    id F = map_filter_on {(x, y). A x y} fst (Z F G) \<and>
    id G = map_filter_on {(x, y). A x y} snd (Z F G)"
    unfolding rel_filter.simps by atomize_elim((rule choice allI)+; auto)
  have id: "eventually P F = eventually P (id F)" "eventually Q G = eventually Q (id G)"
    if "(F, G) \<in> SS'" for P Q F G by simp_all
  show "rel_filter A (Sup S) (Sup S')"
  proof
    let ?Z = "SUP (F, G):SS'. Z F G"
    show *: "\<forall>\<^sub>F (x, y) in ?Z. A x y" using Z by(auto simp add: eventually_Sup)
    show "map_filter_on {(x, y). A x y} fst ?Z = Sup S" "map_filter_on {(x, y). A x y} snd ?Z = Sup S'"
      unfolding filter_eq_iff
      by(auto 4 4 simp add: id eventually_Sup eventually_map_filter_on *[simplified eventually_Sup] simp del: id_apply dest: Z)
  qed
qed

context
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [transfer_rule]: "bi_unique A"
begin

lemma le_filter_parametric [transfer_rule]:
  "(rel_filter A ===> rel_filter A ===> (=)) (\<le>) (\<le>)"
unfolding le_filter_def[abs_def] by transfer_prover

lemma less_filter_parametric [transfer_rule]:
  "(rel_filter A ===> rel_filter A ===> (=)) (<) (<)"
unfolding less_filter_def[abs_def] by transfer_prover

context
  assumes [transfer_rule]: "bi_total A"
begin

lemma Inf_filter_parametric [transfer_rule]:
  "(rel_set (rel_filter A) ===> rel_filter A) Inf Inf"
unfolding Inf_filter_def[abs_def] by transfer_prover

lemma inf_filter_parametric [transfer_rule]:
  "(rel_filter A ===> rel_filter A ===> rel_filter A) inf inf"
proof(intro rel_funI)+
  fix F F' G G'
  assume [transfer_rule]: "rel_filter A F F'" "rel_filter A G G'"
  have "rel_filter A (Inf {F, G}) (Inf {F', G'})" by transfer_prover
  thus "rel_filter A (inf F G) (inf F' G')" by simp
qed

end

end

end

text \<open>Code generation for filters\<close>

definition abstract_filter :: "(unit \<Rightarrow> 'a filter) \<Rightarrow> 'a filter"
  where [simp]: "abstract_filter f = f ()"

code_datatype principal abstract_filter

hide_const (open) abstract_filter

declare [[code drop: filterlim prod_filter filtermap eventually
  "inf :: _ filter \<Rightarrow> _" "sup :: _ filter \<Rightarrow> _" "less_eq :: _ filter \<Rightarrow> _"
  Abs_filter]]

declare filterlim_principal [code]
declare principal_prod_principal [code]
declare filtermap_principal [code]
declare filtercomap_principal [code]
declare eventually_principal [code]
declare inf_principal [code]
declare sup_principal [code]
declare principal_le_iff [code]

lemma Rep_filter_iff_eventually [simp, code]:
  "Rep_filter F P \<longleftrightarrow> eventually P F"
  by (simp add: eventually_def)

lemma bot_eq_principal_empty [code]:
  "bot = principal {}"
  by simp

lemma top_eq_principal_UNIV [code]:
  "top = principal UNIV"
  by simp

instantiation filter :: (equal) equal
begin

definition equal_filter :: "'a filter \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "equal_filter F F' \<longleftrightarrow> F = F'"

lemma equal_filter [code]:
  "HOL.equal (principal A) (principal B) \<longleftrightarrow> A = B"
  by (simp add: equal_filter_def)

instance
  by standard (simp add: equal_filter_def)

end

end
