(* ************************************************************************** *)
(* Title:      Embedded_Algebras.thy                                          *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Embedded_Algebras
  imports Subrings Generated_Groups

begin

section \<open>Definitions\<close>

locale embedded_algebra =
  K?: subfield K R + R?: ring R for K :: "'a set" and R :: "('a, 'b) ring_scheme" (structure)

definition (in ring) line_extension :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "line_extension K a E = (K #> a) <+>\<^bsub>R\<^esub> E"

fun (in ring) Span :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where "Span K Us = foldr (line_extension K) Us { \<zero> }"

fun (in ring) combine :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a"
  where
    "combine (k # Ks) (u # Us) = (k \<otimes> u) \<oplus> (combine Ks Us)"
  | "combine Ks Us = \<zero>"

inductive (in ring) independent :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where
    li_Nil [simp, intro]: "independent K []"
  | li_Cons: "\<lbrakk> u \<in> carrier R; u \<notin> Span K Us; independent K Us \<rbrakk> \<Longrightarrow> independent K (u # Us)"

inductive (in ring) dimension :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    zero_dim [simp, intro]: "dimension 0 K { \<zero> }"
   | Suc_dim: "\<lbrakk> v \<in> carrier R; v \<notin> E; dimension n K E \<rbrakk> \<Longrightarrow> dimension (Suc n) K (line_extension K v E)"


subsubsection \<open>Syntactic Definitions\<close>

abbreviation (in ring) dependent ::  "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "dependent K U \<equiv> \<not> independent K U"

definition over :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "over" 65)
  where "f over a = f a"



context ring
begin


subsection \<open>Basic Properties - First Part\<close>

lemma combine_in_carrier [simp, intro]:
  "\<lbrakk> set Ks \<subseteq> carrier R; set Us \<subseteq> carrier R \<rbrakk> \<Longrightarrow> combine Ks Us \<in> carrier R"
  by (induct Ks Us rule: combine.induct) (auto)

lemma combine_r_distr:
  "\<lbrakk> set Ks \<subseteq> carrier R; set Us \<subseteq> carrier R \<rbrakk> \<Longrightarrow>
     k \<in> carrier R \<Longrightarrow> k \<otimes> (combine Ks Us) = combine (map ((\<otimes>) k) Ks) Us"
  by (induct Ks Us rule: combine.induct) (auto simp add: m_assoc r_distr)

lemma combine_l_distr:
  "\<lbrakk> set Ks \<subseteq> carrier R; set Us \<subseteq> carrier R \<rbrakk> \<Longrightarrow>
     u \<in> carrier R \<Longrightarrow> (combine Ks Us) \<otimes> u = combine Ks (map (\<lambda>u'. u' \<otimes> u) Us)"
  by (induct Ks Us rule: combine.induct) (auto simp add: m_assoc l_distr)

lemma combine_eq_foldr:
  "combine Ks Us = foldr (\<lambda>(k, u). \<lambda>l. (k \<otimes> u) \<oplus> l) (zip Ks Us) \<zero>"
  by (induct Ks Us rule: combine.induct) (auto)

lemma combine_replicate:
  "set Us \<subseteq> carrier R \<Longrightarrow> combine (replicate (length Us) \<zero>) Us = \<zero>"
  by (induct Us) (auto)

lemma combine_append:
  assumes "length Ks = length Us"
    and "set Ks  \<subseteq> carrier R" "set Us \<subseteq> carrier R"
    and "set Ks' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "(combine Ks Us) \<oplus> (combine Ks' Vs) = combine (Ks @ Ks') (Us @ Vs)"
  using assms
proof (induct Ks arbitrary: Us)
  case Nil thus ?case by auto
next
  case (Cons k Ks)
  then obtain u Us' where Us: "Us = u # Us'"
    by (metis length_Suc_conv)
  hence u: "u \<in> carrier R" and Us': "set Us' \<subseteq> carrier R"
    using Cons(4) by auto
  then show ?case
    using combine_in_carrier[OF _ Us', of Ks] Cons
          combine_in_carrier[OF Cons(5-6)] unfolding Us
    by (auto, simp add: add.m_assoc)
qed

lemma combine_add:
  assumes "length Ks = length Us" and "length Ks' = length Us"
    and "set Ks  \<subseteq> carrier R" "set Ks'  \<subseteq> carrier R" "set Us \<subseteq> carrier R"
  shows "(combine Ks Us) \<oplus> (combine Ks' Us) = combine (map2 (\<oplus>) Ks Ks') Us"
  using assms
proof (induct Us arbitrary: Ks Ks')
  case Nil thus ?case by simp
next
  case (Cons u Us)
  then obtain c c' Cs Cs' where Ks: "Ks = c # Cs" and Ks': "Ks' = c' # Cs'"
    by (metis length_Suc_conv)
  hence in_carrier:
    "c  \<in> carrier R" "set Cs  \<subseteq> carrier R"
    "c' \<in> carrier R" "set Cs' \<subseteq> carrier R"
    "u  \<in> carrier R" "set Us  \<subseteq> carrier R"
    using Cons(4-6) by auto
  hence lc_in_carrier: "combine Cs Us \<in> carrier R" "combine Cs' Us \<in> carrier R"
    using combine_in_carrier by auto
  have "combine Ks (u # Us) \<oplus> combine Ks' (u # Us) =
        ((c \<otimes> u) \<oplus> combine Cs Us) \<oplus> ((c' \<otimes> u) \<oplus> combine Cs' Us)"
    unfolding Ks Ks' by auto
  also have " ... = ((c \<oplus> c') \<otimes> u \<oplus> (combine Cs Us \<oplus> combine Cs' Us))"
    using lc_in_carrier in_carrier(1,3,5) by (simp add: l_distr ring_simprules(7,22))
  also have " ... = combine (map2 (\<oplus>) Ks Ks') (u # Us)"
    using Cons unfolding Ks Ks' by auto
  finally show ?case .
qed


subsection \<open>Some Basic Properties of Linear_Ind\<close>

lemma independent_in_carrier: "independent K Us \<Longrightarrow> set Us \<subseteq> carrier R"
  by (induct Us rule: independent.induct) (simp_all)

lemma independent_backwards:
  "independent K (u # Us) \<Longrightarrow> u \<notin> Span K Us"
  "independent K (u # Us) \<Longrightarrow> independent K Us"
  "independent K (u # Us) \<Longrightarrow> u \<in> carrier R"
  by (cases rule: independent.cases, auto)+


text \<open>Now, we fix K, a subfield of the ring. Many lemmas would also be true for weaker
      structures, but our interest is to work with subfields, so generalization could
      be the subjuct of a future work.\<close>

context
  fixes K :: "'a set" assumes K: "subfield K R"
begin


subsection \<open>Basic Properties - Second Part\<close>

lemmas subring_props [simp] =
  subringE[OF subfieldE(1)[OF K]]

lemma line_extension_mem_iff: "u \<in> line_extension K a E \<longleftrightarrow> (\<exists>k \<in> K. \<exists>v \<in> E. u = k \<otimes> a \<oplus> v)"
  unfolding line_extension_def set_add_def'[of R "K #> a" E] unfolding r_coset_def by blast

lemma line_extension_is_subgroup:
  assumes "subgroup E (add_monoid R)" "a \<in> carrier R"
  shows "subgroup (line_extension K a E) (add_monoid R)"
proof (rule add.subgroupI)
  show "line_extension K a E \<subseteq> carrier R"
    by (simp add: assms add.subgroupE(1) line_extension_def r_coset_subset_G set_add_closed)
next
  have "\<zero> = \<zero> \<otimes> a \<oplus> \<zero>"
    using assms(2) by simp
  hence "\<zero> \<in> line_extension K a E"
    using line_extension_mem_iff subgroup.one_closed[OF assms(1)] by auto
  thus "line_extension K a E \<noteq> {}" by auto
next
  fix u1 u2
  assume "u1 \<in> line_extension K a E" and "u2 \<in> line_extension K a E"
  then obtain k1 k2 v1 v2
    where u1: "k1 \<in> K" "v1 \<in> E" "u1 = (k1 \<otimes> a) \<oplus> v1"
      and u2: "k2 \<in> K" "v2 \<in> E" "u2 = (k2 \<otimes> a) \<oplus> v2"
      and in_carr: "k1 \<in> carrier R" "v1 \<in> carrier R" "k2 \<in> carrier R" "v2 \<in> carrier R"
    using line_extension_mem_iff by (meson add.subgroupE(1)[OF assms(1)] subring_props(1) subsetCE)

  hence "u1 \<oplus> u2 = ((k1 \<oplus> k2) \<otimes> a) \<oplus> (v1 \<oplus> v2)"
    using assms(2) by algebra
  moreover have "k1 \<oplus> k2 \<in> K" and "v1 \<oplus> v2 \<in> E"
    using add.subgroupE(4)[OF assms(1)] u1 u2 by auto
  ultimately show "u1 \<oplus> u2 \<in> line_extension K a E"
    using line_extension_mem_iff by auto

  have "\<ominus> u1 = ((\<ominus> k1) \<otimes> a) \<oplus> (\<ominus> v1)"
    using in_carr(1-2) u1(3) assms(2) by algebra
  moreover have "\<ominus> k1 \<in> K" and "\<ominus> v1 \<in> E"
    using add.subgroupE(3)[OF assms(1)] u1 by auto
  ultimately show "(\<ominus> u1) \<in> line_extension K a E"
    using line_extension_mem_iff by auto
qed

corollary Span_is_add_subgroup:
  "set Us \<subseteq> carrier R \<Longrightarrow> subgroup (Span K Us) (add_monoid R)"
  using line_extension_is_subgroup add.normal_invE(1)[OF add.one_is_normal] by (induct Us) (auto)

lemma line_extension_smult_closed:
  assumes "\<And>k v. \<lbrakk> k \<in> K; v \<in> E \<rbrakk> \<Longrightarrow> k \<otimes> v \<in> E" and "E \<subseteq> carrier R" "a \<in> carrier R"
  shows "\<And>k u. \<lbrakk> k \<in> K; u \<in> line_extension K a E \<rbrakk> \<Longrightarrow> k \<otimes> u \<in> line_extension K a E"
proof -
  fix k u assume A: "k \<in> K" "u \<in> line_extension K a E"
  then obtain k' v'
    where u: "k' \<in> K" "v' \<in> E" "u = k' \<otimes> a \<oplus> v'"
      and in_carr: "k \<in> carrier R" "k' \<in> carrier R" "v' \<in> carrier R"
    using line_extension_mem_iff assms(2) by (meson subring_props(1) subsetCE)
  hence "k \<otimes> u = (k \<otimes> k') \<otimes> a \<oplus> (k \<otimes> v')"
    using assms(3) by algebra
  thus "k \<otimes> u \<in> line_extension K a E"
    using assms(1)[OF A(1) u(2)] line_extension_mem_iff u(1) A(1) by auto
qed

lemma Span_subgroup_props [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "Span K Us \<subseteq> carrier R"
    and "\<zero> \<in> Span K Us"
    and "\<And>v1 v2. \<lbrakk> v1 \<in> Span K Us; v2 \<in> Span K Us \<rbrakk> \<Longrightarrow> (v1 \<oplus> v2) \<in> Span K Us"
    and "\<And>v. v \<in> Span K Us \<Longrightarrow> (\<ominus> v) \<in> Span K Us"
  using add.subgroupE subgroup.one_closed[of _ "add_monoid R"]
        Span_is_add_subgroup[OF assms(1)] by auto

lemma Span_smult_closed [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "\<And>k v. \<lbrakk> k \<in> K; v \<in> Span K Us \<rbrakk> \<Longrightarrow> k \<otimes> v \<in> Span K Us"
  using assms
proof (induct Us)
  case Nil thus ?case
    using r_null subring_props(1) by (auto, blast)
next
  case Cons thus ?case
    using Span_subgroup_props(1) line_extension_smult_closed by auto
qed

lemma Span_m_inv_simprule [simp]:
  assumes "set Us \<subseteq> carrier R"
  shows "\<lbrakk> k \<in> K - { \<zero> }; a \<in> carrier R \<rbrakk> \<Longrightarrow> k \<otimes> a \<in> Span K Us \<Longrightarrow> a \<in> Span K Us"
proof -
  assume k: "k \<in> K - { \<zero> }" and a: "a \<in> carrier R" and ka: "k \<otimes> a \<in> Span K Us"
  have inv_k: "inv k \<in> K" "inv k \<otimes> k = \<one>"
    using subfield_m_inv[OF K k] by simp+
  hence "inv k \<otimes> (k \<otimes> a) \<in> Span K Us"
    using Span_smult_closed[OF assms _ ka] by simp
  thus ?thesis
    using inv_k subring_props(1)a k by (smt DiffD1 l_one m_assoc set_rev_mp)
qed


subsection \<open>Span as Linear Combinations\<close>

text \<open>We show that Span is the set of linear combinations\<close>

lemma line_extension_of_combine_set:
  assumes "u \<in> carrier R"
  shows "line_extension K u { combine Ks Us | Ks. set Ks \<subseteq> K } = 
                { combine Ks (u # Us) | Ks. set Ks \<subseteq> K }"
  (is "?line_extension = ?combinations")
proof
  show "?line_extension \<subseteq> ?combinations"
  proof
    fix v assume "v \<in> ?line_extension"
    then obtain k Ks
      where "k \<in> K" "set Ks \<subseteq> K" and "v = combine (k # Ks) (u # Us)"
      using line_extension_mem_iff by auto
    thus "v \<in> ?combinations"
      by (metis (mono_tags, lifting) insert_subset list.simps(15) mem_Collect_eq)
  qed
next
  show "?combinations \<subseteq> ?line_extension"
  proof
    fix v assume "v \<in> ?combinations"
    then obtain Ks where v: "set Ks \<subseteq> K" "v = combine Ks (u # Us)"
      by auto
    thus "v \<in> ?line_extension"
    proof (cases Ks)
      case Cons thus ?thesis
        using v line_extension_mem_iff by auto
    next
      case Nil
      hence "v = \<zero>"
        using v by simp
      moreover have "combine [] Us = \<zero>" by simp
      hence "\<zero> \<in> { combine Ks Us | Ks. set Ks \<subseteq> K }"
        by (metis (mono_tags, lifting) local.Nil mem_Collect_eq v(1))
      hence "(\<zero> \<otimes> u) \<oplus> \<zero> \<in> ?line_extension"
        using line_extension_mem_iff subring_props(2) by blast
      hence "\<zero> \<in> ?line_extension"
        using assms by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma Span_eq_combine_set:
  assumes "set Us \<subseteq> carrier R" shows "Span K Us = { combine Ks Us | Ks. set Ks \<subseteq> K }"
  using assms line_extension_of_combine_set
  by (induct Us) (auto, metis empty_set empty_subsetI)

lemma line_extension_of_combine_set_length_version:
  assumes "u \<in> carrier R"
  shows "line_extension K u { combine Ks Us | Ks. length Ks = length Us \<and> set Ks \<subseteq> K } = 
                      { combine Ks (u # Us) | Ks. length Ks = length (u # Us) \<and> set Ks \<subseteq> K }"
  (is "?line_extension = ?combinations")
proof
  show "?line_extension \<subseteq> ?combinations"
  proof
    fix v assume "v \<in> ?line_extension"
    then obtain k Ks
      where "v = combine (k # Ks) (u # Us)" "length (k # Ks) = length (u # Us)" "set (k # Ks) \<subseteq> K"
      using line_extension_mem_iff by auto
    thus "v \<in> ?combinations" by blast
  qed
next
  show "?combinations \<subseteq> ?line_extension"
  proof
    fix c assume "c \<in> ?combinations"
    then obtain Ks where c: "c = combine Ks (u # Us)" "length Ks = length (u # Us)" "set Ks \<subseteq> K"
      by blast
    then obtain k Ks' where k: "Ks = k # Ks'"
      by (metis length_Suc_conv)
    thus "c \<in> ?line_extension"
      using c line_extension_mem_iff unfolding k by auto
  qed
qed

lemma Span_eq_combine_set_length_version:
  assumes "set Us \<subseteq> carrier R"
  shows "Span K Us = { combine Ks Us | Ks. length Ks = length Us \<and> set Ks \<subseteq> K }"
  using assms line_extension_of_combine_set_length_version by (induct Us) (auto)


subsubsection \<open>Corollaries\<close>

corollary Span_mem_iff:
  assumes "set Us \<subseteq> carrier R" and "a \<in> carrier R"
  shows "a \<in> Span K Us \<longleftrightarrow> (\<exists>k \<in> K - { \<zero> }. \<exists>Ks. set Ks \<subseteq> K \<and> combine (k # Ks) (a # Us) = \<zero>)"
         (is "?in_Span \<longleftrightarrow> ?exists_combine")
proof 
  assume "?in_Span"
  then obtain Ks where Ks: "set Ks \<subseteq> K" "a = combine Ks Us"
    using Span_eq_combine_set[OF assms(1)] by auto
  hence "((\<ominus> \<one>) \<otimes> a) \<oplus> a = combine ((\<ominus> \<one>) # Ks) (a # Us)"
    by auto
  moreover have "((\<ominus> \<one>) \<otimes> a) \<oplus> a = \<zero>"
    using assms(2) l_minus l_neg by auto  
  moreover have "\<ominus> \<one> \<noteq> \<zero>"
    using subfieldE(6)[OF K] l_neg by force 
  ultimately show "?exists_combine"
    using subring_props(3,5) Ks(1) by (force simp del: combine.simps)
next
  assume "?exists_combine"
  then obtain k Ks
    where k: "k \<in> K" "k \<noteq> \<zero>" and Ks: "set Ks \<subseteq> K" and a: "(k \<otimes> a) \<oplus> combine Ks Us = \<zero>"
    by auto
  hence "combine Ks Us \<in> Span K Us"
    using Span_eq_combine_set[OF assms(1)] by auto
  hence "k \<otimes> a \<in> Span K Us"
    using Span_subgroup_props[OF assms(1)] k Ks a
    by (metis (no_types, lifting) assms(2) contra_subsetD m_closed minus_equality subring_props(1))
  thus "?in_Span"
    using Span_m_inv_simprule[OF assms(1) _ assms(2), of k] k by auto
qed

corollary Span_mem_iff_length_version:
  assumes "set Us \<subseteq> carrier R"
  shows "a \<in> Span K Us \<longleftrightarrow> (\<exists>Ks. set Ks \<subseteq> K \<and> length Ks = length Us \<and> a = combine Ks Us)"
  using Span_eq_combine_set_length_version[OF assms] by blast


subsection \<open>Span as the minimal subgroup that contains K <#> (set Us)\<close>

text \<open>Now we show the link between Span and Group.generate\<close>

lemma mono_Span:
  assumes "set Us \<subseteq> carrier R" and "u \<in> carrier R"
  shows "Span K Us \<subseteq> Span K (u # Us)"
proof
  fix v assume v: "v \<in> Span K Us"
  hence "(\<zero> \<otimes> u) \<oplus> v \<in> Span K (u # Us)"
    using line_extension_mem_iff by auto
  thus "v \<in> Span K (u # Us)"
    using Span_subgroup_props(1)[OF assms(1)] assms(2) v
    by (auto simp del: Span.simps)
qed

lemma Span_min:
  assumes "set Us \<subseteq> carrier R" and "subgroup E (add_monoid R)"
  shows "K <#> (set Us) \<subseteq> E \<Longrightarrow> Span K Us \<subseteq> E"
proof -
  assume "K <#> (set Us) \<subseteq> E" show "Span K Us \<subseteq> E"
  proof
    fix v assume "v \<in> Span K Us"
    then obtain Ks where v: "set Ks \<subseteq> K" "v = combine Ks Us"
      using Span_eq_combine_set[OF assms(1)] by auto
    from \<open>set Ks \<subseteq> K\<close> \<open>set Us \<subseteq> carrier R\<close> and \<open>K <#> (set Us) \<subseteq> E\<close>
    show "v \<in> E" unfolding v(2)
    proof (induct Ks Us rule: combine.induct)
      case (1 k Ks u Us)
      hence "k \<in> K" and "u \<in> set (u # Us)" by auto
      hence "k \<otimes> u \<in> E" 
        using 1(4) unfolding set_mult_def by auto
      moreover have "K <#> set Us \<subseteq> E"
        using 1(4) unfolding set_mult_def by auto
      hence "combine Ks Us \<in> E"
        using 1 by auto
      ultimately show ?case
        using add.subgroupE(4)[OF assms(2)] by auto 
    next
      case "2_1" thus ?case
        using subgroup.one_closed[OF assms(2)] by auto
    next
      case  "2_2" thus ?case
        using subgroup.one_closed[OF assms(2)] by auto
    qed
  qed
qed

lemma Span_eq_generate:
  assumes "set Us \<subseteq> carrier R" shows "Span K Us = generate (add_monoid R) (K <#> (set Us))"
proof (rule add.generateI)
  show "K <#> set Us \<subseteq> carrier R"
    using subring_props(1) assms unfolding set_mult_def by blast
next
  show "subgroup (Span K Us) (add_monoid R)"
    using Span_is_add_subgroup[OF assms] .
next
  show "\<And>E. \<lbrakk> subgroup E (add_monoid R); K <#> set Us \<subseteq> E \<rbrakk> \<Longrightarrow> Span K Us \<subseteq> E"
    using Span_min assms by blast
next
  show "K <#> set Us \<subseteq> Span K Us"
  using assms
  proof (induct Us)
    case Nil thus ?case
      unfolding set_mult_def by auto
  next
    case (Cons u Us)
    have "K <#> set (u # Us) = (K <#> { u }) \<union> (K <#> set Us)"
      unfolding set_mult_def by auto
    moreover have "\<And>k. k \<in> K \<Longrightarrow> k \<otimes> u \<in> Span K (u # Us)"
    proof -
      fix k assume k: "k \<in> K"
      hence "combine [ k ] (u # Us) \<in> Span K (u # Us)"
        using Span_eq_combine_set[OF Cons(2)] by (auto simp del: combine.simps)
      moreover have "k \<in> carrier R" and "u \<in> carrier R"
        using Cons(2) k subring_props(1) by (blast, auto) 
      ultimately show "k \<otimes> u \<in> Span K (u # Us)"
        by (auto simp del: Span.simps)
    qed
    hence "K <#> { u } \<subseteq> Span K (u # Us)"
      unfolding set_mult_def by auto
    moreover have "K <#> set Us \<subseteq> Span K (u # Us)"
      using mono_Span[of Us u] Cons by (auto simp del: Span.simps)
    ultimately show ?case
      using Cons by (auto simp del: Span.simps)
  qed
qed


subsubsection \<open>Corollaries\<close>

corollary Span_same_set:
  assumes "set Us \<subseteq> carrier R"
  shows "set Us = set Vs \<Longrightarrow> Span K Us = Span K Vs"
  using Span_eq_generate assms by auto 

corollary Span_incl: "set Us \<subseteq> carrier R \<Longrightarrow> K <#> (set Us) \<subseteq> Span K Us"
  using Span_eq_generate generate.incl[of _ _ "add_monoid R"] by auto

corollary Span_base_incl: "set Us \<subseteq> carrier R \<Longrightarrow> set Us \<subseteq> Span K Us"
proof -
  assume A: "set Us \<subseteq> carrier R"
  hence "{ \<one> } <#> set Us = set Us"
    unfolding set_mult_def by force
  moreover have "{ \<one> } <#> set Us \<subseteq> K <#> set Us"
    using subring_props(3) unfolding set_mult_def by blast
  ultimately show ?thesis
    using Span_incl[OF A] by auto
qed

corollary mono_Span_sublist:
  assumes "set Us \<subseteq> set Vs" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K Vs"
  using add.mono_generate[OF mono_set_mult[OF _ assms(1), of K K R]
        set_mult_closed[OF subring_props(1) assms(2)]]
        Span_eq_generate[OF assms(2)] Span_eq_generate[of Us] assms by auto

corollary mono_Span_append:
  assumes "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K (Us @ Vs)"
    and "Span K Us \<subseteq> Span K (Vs @ Us)"
  using mono_Span_sublist[of Us "Us @ Vs"] assms
        Span_same_set[of "Us @ Vs" "Vs @ Us"] by auto

corollary mono_Span_subset:
  assumes "set Us \<subseteq> Span K Vs" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subseteq> Span K Vs"
proof (rule Span_min[OF _ Span_is_add_subgroup[OF assms(2)]])
  show "set Us \<subseteq> carrier R"
    using Span_subgroup_props(1)[OF assms(2)] assms by auto
  show "K <#> set Us \<subseteq> Span K Vs"
    using Span_smult_closed[OF assms(2)] assms(1) unfolding set_mult_def by blast
qed

lemma Span_strict_incl:
  assumes "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
  shows "Span K Us \<subset> Span K Vs \<Longrightarrow> (\<exists>v \<in> set Vs. v \<notin> Span K Us)"
proof -
  assume "Span K Us \<subset> Span K Vs" show "\<exists>v \<in> set Vs. v \<notin> Span K Us"
  proof (rule ccontr)
    assume "\<not> (\<exists>v \<in> set Vs. v \<notin> Span K Us)"
    hence "Span K Vs \<subseteq> Span K Us"
      using mono_Span_subset[OF _ assms(1), of Vs] by auto
    from \<open>Span K Us \<subset> Span K Vs\<close> and \<open>Span K Vs \<subseteq> Span K Us\<close>
    show False by simp
  qed
qed

lemma Span_append_eq_set_add:
  assumes "set Us \<subseteq> carrier R" and "set Vs \<subseteq> carrier R"
  shows "Span K (Us @ Vs) = (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
  using assms
proof (induct Us)
  case Nil thus ?case
    using Span_subgroup_props(1)[OF Nil(2)] unfolding set_add_def' by force
next
  case (Cons u Us)
  hence in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
    by auto

  have "line_extension K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs) = (Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs)"
  proof
    show "line_extension K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs) \<subseteq> (Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs)"
    proof
      fix v assume "v \<in> line_extension K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
      then obtain k u' v'
        where v: "k \<in> K" "u' \<in> Span K Us" "v' \<in> Span K Vs" "v = k \<otimes> u \<oplus> (u' \<oplus> v')"
        using line_extension_mem_iff[of v u "Span K Us <+>\<^bsub>R\<^esub> Span K Vs"]
        unfolding set_add_def' by blast
      hence "v = (k \<otimes> u \<oplus> u') \<oplus> v'"
        using in_carrier(2-3)[THEN Span_subgroup_props(1)] in_carrier(1) subring_props(1)
        by (metis (no_types, lifting) rev_subsetD ring_simprules(7) semiring_simprules(3))
      moreover have "k \<otimes> u \<oplus> u' \<in> Span K (u # Us)"
        using line_extension_mem_iff v(1-2) by auto
      ultimately show "v \<in> Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs"
        unfolding set_add_def' using v(3) by auto
    qed
  next
    show "Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs \<subseteq> line_extension K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
    proof
      fix v assume "v \<in> Span K (u # Us) <+>\<^bsub>R\<^esub> Span K Vs"
      then obtain k u' v'
        where v: "k \<in> K" "u' \<in> Span K Us" "v' \<in> Span K Vs" "v = (k \<otimes> u \<oplus> u') \<oplus> v'"
        using line_extension_mem_iff[of _ u "Span K Us"] unfolding set_add_def' by auto
      hence "v = (k \<otimes> u) \<oplus> (u' \<oplus> v')"
        using in_carrier(2-3)[THEN Span_subgroup_props(1)] in_carrier(1) subring_props(1)
        by (metis (no_types, lifting) rev_subsetD ring_simprules(5,7))
      thus "v \<in> line_extension K u (Span K Us <+>\<^bsub>R\<^esub> Span K Vs)"
        using line_extension_mem_iff[of "(k \<otimes> u) \<oplus> (u' \<oplus> v')" u "Span K Us <+>\<^bsub>R\<^esub> Span K Vs"]
        unfolding set_add_def' using v by auto
    qed
  qed
  thus ?case
    using Cons by auto
qed


subsection \<open>Characterisation of Linearly Independent "Sets"\<close>

declare independent_backwards [intro]
declare independent_in_carrier [intro]

lemma independent_distinct: "independent K Us \<Longrightarrow> distinct Us"
proof (induct Us rule: list.induct)
  case Nil thus ?case by simp
next
  case Cons thus ?case
    using independent_backwards[OF Cons(2)]
          independent_in_carrier[OF Cons(2)]
          Span_base_incl
    by auto
qed

lemma independent_strinct_incl:
  assumes "independent K (u # Us)" shows "Span K Us \<subset> Span K (u # Us)"
proof -
  have "u \<in> Span K (u # Us)"
    using Span_base_incl[OF independent_in_carrier[OF assms]] by auto
  moreover have "Span K Us \<subseteq> Span K (u # Us)"
    using mono_Span independent_in_carrier[OF assms] by auto
  ultimately show ?thesis
    using independent_backwards(1)[OF assms] by auto 
qed

corollary independent_replacement:
  assumes "independent K (u # Us)" and "independent K Vs"
  shows "Span K (u # Us) \<subseteq> Span K Vs \<Longrightarrow> (\<exists>v \<in> set Vs. independent K (v # Us))"
proof -
  assume "Span K (u # Us) \<subseteq> Span K Vs"
  hence "Span K Us \<subset> Span K Vs"
    using independent_strinct_incl[OF assms(1)] by auto
  then obtain v where v: "v \<in> set Vs" "v \<notin> Span K Us"
    using Span_strict_incl[of Us Vs] assms[THEN independent_in_carrier] by auto
  thus ?thesis
    using li_Cons[of v K Us] assms independent_in_carrier[OF assms(2)] by auto
qed

lemma independent_split:
  assumes "independent K (Us @ Vs)"
  shows "independent K Vs"
    and "independent K Us"
    and "Span K Us \<inter> Span K Vs = { \<zero> }"
proof -
  from assms show "independent K Vs"
    by (induct Us) (auto)
next
  from assms show "independent K Us"
  proof (induct Us)
    case Nil thus ?case by simp
  next
    case (Cons u Us')
    hence u: "u \<in> carrier R" and "set Us' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
      using independent_in_carrier[of K "(u # Us') @ Vs"] by auto
    hence "Span K Us' \<subseteq> Span K (Us' @ Vs)"
      using mono_Span_append(1) by simp
    thus ?case
      using independent_backwards[of K u "Us' @ Vs"] Cons li_Cons[OF u] by auto
  qed
next
  from assms show "Span K Us \<inter> Span K Vs = { \<zero> }"
  proof (induct Us rule: list.induct)
    case Nil thus ?case
      using Span_subgroup_props(2)[OF independent_in_carrier[of K Vs]] by simp 
  next
    case (Cons u Us)
    hence IH: "Span K Us \<inter> Span K Vs = {\<zero>}" by auto
    have in_carrier:
      "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R" "set (u # Us) \<subseteq> carrier R"
      using Cons(2)[THEN independent_in_carrier] by auto
    hence "{ \<zero> } \<subseteq> Span K (u # Us) \<inter> Span K Vs"
      using in_carrier(3-4)[THEN Span_subgroup_props(2)] by auto

    moreover have "Span K (u # Us) \<inter> Span K Vs \<subseteq> { \<zero> }"
    proof (rule ccontr)
      assume "\<not> Span K (u # Us) \<inter> Span K Vs \<subseteq> {\<zero>}"
      hence "\<exists>a. a \<noteq> \<zero> \<and> a \<in> Span K (u # Us) \<and> a \<in> Span K Vs" by auto
      then obtain k u' v'
        where u': "u' \<in> Span K Us" "u' \<in> carrier R"
          and v': "v' \<in> Span K Vs" "v' \<in> carrier R" "v' \<noteq> \<zero>"
          and k: "k \<in> K" "(k \<otimes> u \<oplus> u') = v'"
        using line_extension_mem_iff[of _ u "Span K Us"] in_carrier(2-3)[THEN Span_subgroup_props(1)]
              subring_props(1) by force
      hence "v' = \<zero>" if "k = \<zero>"
        using in_carrier(1) that IH by auto
      hence diff_zero: "k \<noteq> \<zero>" using v'(3) by auto

      have "k \<in> carrier R"
        using subring_props(1) k(1) by blast
      hence "k \<otimes> u = (\<ominus> u') \<oplus> v'"
        using in_carrier(1) k(2) u'(2) v'(2) add.m_comm r_neg1 by auto
      hence "k \<otimes> u \<in> Span K (Us @ Vs)"
        using Span_subgroup_props(4)[OF in_carrier(2) u'(1)] v'(1) 
              Span_append_eq_set_add[OF in_carrier(2-3)] unfolding set_add_def' by blast
      hence "u \<in> Span K (Us @ Vs)"
        using Cons(2) Span_m_inv_simprule[OF _ _ in_carrier(1), of "Us @ Vs" k]
              diff_zero k(1) in_carrier(2-3) by auto
      moreover have "u \<notin> Span K (Us @ Vs)"
        using independent_backwards(1)[of K u "Us @ Vs"] Cons(2) by auto
      ultimately show False by simp
    qed

    ultimately show ?case by auto
  qed
qed

lemma independent_append:
  assumes "independent K Us" and "independent K Vs" and "Span K Us \<inter> Span K Vs = { \<zero> }"
  shows "independent K (Us @ Vs)"
  using assms
proof (induct Us rule: list.induct)
  case Nil thus ?case by simp
next
  case (Cons u Us)
  hence in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Vs \<subseteq> carrier R" "set (u # Us) \<subseteq> carrier R"
    using Cons(2-3)[THEN independent_in_carrier] by auto
  hence "Span K Us \<subseteq> Span K (u # Us)" 
    using mono_Span by auto
  hence "Span K Us \<inter> Span K Vs = { \<zero> }"
    using Cons(4) Span_subgroup_props(2)[OF in_carrier(2)] by auto
  hence "independent K (Us @ Vs)"
    using Cons by auto
  moreover have "u \<notin> Span K (Us @ Vs)"
  proof (rule ccontr)
    assume "\<not> u \<notin> Span K (Us @ Vs)"
    then obtain u' v'
      where u': "u' \<in> Span K Us" "u' \<in> carrier R"
        and v': "v' \<in> Span K Vs" "v' \<in> carrier R" and u:"u = u' \<oplus> v'"
      using Span_append_eq_set_add[OF in_carrier(2-3)] in_carrier(2-3)[THEN Span_subgroup_props(1)]
      unfolding set_add_def' by blast
    hence "u \<oplus> (\<ominus> u') = v'"
      using in_carrier(1) by algebra
    moreover have "u \<in> Span K (u # Us)" and "u' \<in> Span K (u # Us)"
      using Span_base_incl[OF in_carrier(4)] mono_Span[OF in_carrier(2,1)] u'(1)
      by (auto simp del: Span.simps)
    hence "u \<oplus> (\<ominus> u') \<in> Span K (u # Us)"
      using Span_subgroup_props(3-4)[OF in_carrier(4)] by (auto simp del: Span.simps)
    ultimately have "u \<oplus> (\<ominus> u') = \<zero>"
      using Cons(4) v'(1) by auto
    hence "u = u'"
      using Cons(4) v'(1) in_carrier(1) u'(2) \<open>u \<oplus> \<ominus> u' = v'\<close> u by auto
    thus False
      using u'(1) independent_backwards(1)[OF Cons(2)] by simp
  qed
  ultimately show ?case
    using in_carrier(1) li_Cons by simp
qed

lemma independent_imp_trivial_combine:
  assumes "independent K Us"
  shows "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; combine Ks Us = \<zero> \<rbrakk> \<Longrightarrow> set (take (length Us) Ks) \<subseteq> { \<zero> }"
  using assms
proof (induct Us rule: list.induct)
  case Nil thus ?case by simp
next
  case (Cons u Us) thus ?case
  proof (cases "Ks = []")
    assume "Ks = []" thus ?thesis by auto
  next
    assume "Ks \<noteq> []"
    then obtain k Ks' where k: "k \<in> K" and Ks': "set Ks' \<subseteq> K" and Ks: "Ks = k # Ks'"
      using Cons(2) by (metis insert_subset list.exhaust_sel list.simps(15))
    hence Us: "set Us \<subseteq> carrier R" and u: "u \<in> carrier R"
      using independent_in_carrier[OF Cons(4)] by auto
    have "u \<in> Span K Us" if "k \<noteq> \<zero>"
      using that Span_mem_iff[OF Us u] Cons(3-4) Ks' k unfolding Ks by blast
    hence k_zero: "k = \<zero>"
      using independent_backwards[OF Cons(4)] by blast
    hence "combine Ks' Us = \<zero>"
      using combine_in_carrier[OF _ Us, of Ks'] Ks' u Cons(3) subring_props(1) unfolding Ks by auto
    hence "set (take (length Us) Ks') \<subseteq> { \<zero> }"
      using Cons(1)[OF Ks' _ independent_backwards(2)[OF Cons(4)]] by simp 
    thus ?thesis
      using k_zero unfolding Ks by auto
  qed
qed

lemma trivial_combine_imp_independent:
  assumes "set Us \<subseteq> carrier R"
    and "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; combine Ks Us = \<zero> \<rbrakk> \<Longrightarrow> set (take (length Us) Ks) \<subseteq> { \<zero> }"
  shows "independent K Us"
  using assms
proof (induct Us)
  case Nil thus ?case by simp
next
  case (Cons u Us)
  hence Us: "set Us \<subseteq> carrier R" and u: "u \<in> carrier R" by auto

  have "\<And>Ks. \<lbrakk> set Ks \<subseteq> K; combine Ks Us = \<zero> \<rbrakk> \<Longrightarrow> set (take (length Us) Ks) \<subseteq> { \<zero> }"
  proof -
    fix Ks assume Ks: "set Ks \<subseteq> K" and lin_c: "combine Ks Us = \<zero>"
    hence "combine (\<zero> # Ks) (u # Us) = \<zero>"
      using u subring_props(1) combine_in_carrier[OF _ Us] by auto
    hence "set (take (length (u # Us)) (\<zero> # Ks)) \<subseteq> { \<zero> }"
      using Cons(3)[of "\<zero> # Ks"] subring_props(2) Ks by auto
    thus "set (take (length Us) Ks) \<subseteq> { \<zero> }" by auto
  qed
  hence "independent K Us"
    using Cons(1)[OF Us] by simp

  moreover have "u \<notin> Span K Us"
  proof (rule ccontr)
    assume "\<not> u \<notin> Span K Us"
    then obtain k Ks where k: "k \<in> K" "k \<noteq> \<zero>" and Ks: "set Ks \<subseteq> K" and u: "combine (k # Ks) (u # Us) = \<zero>"
      using Span_mem_iff[OF Us u] by auto
    have "set (take (length (u # Us)) (k # Ks)) \<subseteq> { \<zero> }"
      using Cons(3)[OF _ u] k(1) Ks by auto
    hence "k = \<zero>" by auto
    from \<open>k = \<zero>\<close> and \<open>k \<noteq> \<zero>\<close> show False by simp
  qed

  ultimately show ?case
    using li_Cons[OF u] by simp
qed

corollary unique_decomposition:
  assumes "independent K Us"
  shows "a \<in> Span K Us \<Longrightarrow> \<exists>!Ks. set Ks \<subseteq> K \<and> length Ks = length Us \<and> a = combine Ks Us"
proof -
  note in_carrier = independent_in_carrier[OF assms]

  assume "a \<in> Span K Us"
  then obtain Ks where Ks: "set Ks \<subseteq> K" "length Ks = length Us" "a = combine Ks Us"
    using Span_mem_iff_length_version[OF in_carrier] by blast

  moreover
  have "\<And>Ks'. \<lbrakk> set Ks' \<subseteq> K; length Ks' = length Us; a = combine Ks' Us \<rbrakk> \<Longrightarrow> Ks = Ks'"
  proof -
    fix Ks' assume Ks': "set Ks' \<subseteq> K" "length Ks' = length Us" "a = combine Ks' Us"
    hence set_Ks: "set Ks \<subseteq> carrier R" and set_Ks': "set Ks' \<subseteq> carrier R"
      using subring_props(1) Ks(1) by blast+
    have same_length: "length Ks = length Ks'"
      using Ks Ks' by simp

    have "(combine Ks Us) \<oplus> ((\<ominus> \<one>) \<otimes> (combine Ks' Us)) = \<zero>"
      using combine_in_carrier[OF set_Ks  in_carrier]
            combine_in_carrier[OF set_Ks' in_carrier] Ks(3) Ks'(3) by algebra
    hence "(combine Ks Us) \<oplus> (combine (map ((\<otimes>) (\<ominus> \<one>)) Ks') Us) = \<zero>"
      using combine_r_distr[OF set_Ks' in_carrier, of "\<ominus> \<one>"] subring_props by auto
    moreover have set_map: "set (map ((\<otimes>) (\<ominus> \<one>)) Ks') \<subseteq> K"
      using Ks'(1) subring_props by (induct Ks') (auto)
    hence "set (map ((\<otimes>) (\<ominus> \<one>)) Ks') \<subseteq> carrier R"
      using subring_props(1) by blast
    ultimately have "combine (map2 (\<oplus>) Ks (map ((\<otimes>) (\<ominus> \<one>)) Ks')) Us = \<zero>"
      using combine_add[OF Ks(2) _ set_Ks _ in_carrier, of "map ((\<otimes>) (\<ominus> \<one>)) Ks'"] Ks'(2) by auto
    moreover have "set (map2 (\<oplus>) Ks (map ((\<otimes>) (\<ominus> \<one>)) Ks')) \<subseteq> K"
      using Ks(1) set_map subring_props(7)
      by (induct Ks) (auto, metis contra_subsetD in_set_zipE local.set_map set_ConsD subring_props(7))
    ultimately have "set (take (length Us) (map2 (\<oplus>) Ks (map ((\<otimes>) (\<ominus> \<one>)) Ks'))) \<subseteq> { \<zero> }"
      using independent_imp_trivial_combine[OF assms] by auto
    hence "set (map2 (\<oplus>) Ks (map ((\<otimes>) (\<ominus> \<one>)) Ks')) \<subseteq> { \<zero> }"
      using Ks(2) Ks'(2) by auto
    thus "Ks = Ks'"
      using set_Ks set_Ks' same_length
    proof (induct Ks arbitrary: Ks')
      case Nil thus?case by simp
    next
      case (Cons k Ks)
      then obtain k' Ks'' where k': "Ks' = k' # Ks''"
        by (metis Suc_length_conv)
      have "Ks = Ks''"
        using Cons unfolding k' by auto
      moreover have "k = k'"
        using Cons(2-4) l_minus minus_equality unfolding k' by (auto, fastforce)
      ultimately show ?case
        unfolding k' by simp
    qed
  qed

  ultimately show ?thesis by blast
qed


subsection \<open>Replacement Theorem\<close>

lemma independent_rotate1_aux:
  "independent K (u # Us @ Vs) \<Longrightarrow> independent K ((Us @ [u]) @ Vs)"
proof -
  assume "independent K (u # Us @ Vs)"
  hence li: "independent K [u]" "independent K Us" "independent K Vs"
    and inter: "Span K [u] \<inter> Span K Us = { \<zero> }"
               "Span K (u # Us) \<inter> Span K Vs = { \<zero> }"
    using independent_split[of "u # Us" Vs] independent_split[of "[u]" Us] by auto
  hence "independent K (Us @ [u])"
    using independent_append[OF li(2,1)] by auto
  moreover have "Span K (Us @ [u]) \<inter> Span K Vs = { \<zero> }"
    using Span_same_set[of "u # Us" "Us @ [u]"] li(1-2)[THEN independent_in_carrier] inter(2) by auto
  ultimately show "independent K ((Us @ [u]) @ Vs)"
    using independent_append[OF _ li(3), of "Us @ [u]"] by simp
qed

corollary independent_rotate1:
  "independent K (Us @ Vs) \<Longrightarrow> independent K ((rotate1 Us) @ Vs)"
  using independent_rotate1_aux by (cases Us) (auto)

(*
corollary independent_rotate:
  "independent K (Us @ Vs) \<Longrightarrow> independent K ((rotate n Us) @ Vs)"
  using independent_rotate1 by (induct n) auto

lemma rotate_append: "rotate (length l) (l @ q) = q @ l"
  by (induct l arbitrary: q) (auto simp add: rotate1_rotate_swap)
*)

corollary independent_same_set:
  assumes "set Us = set Vs" and "length Us = length Vs"
  shows "independent K Us \<Longrightarrow> independent K Vs"
proof -
  assume "independent K Us" thus ?thesis
    using assms
  proof (induct Us arbitrary: Vs rule: list.induct)
    case Nil thus ?case by simp
  next
    case (Cons u Us)
    then obtain Vs' Vs'' where Vs: "Vs = Vs' @ (u # Vs'')"
      by (metis list.set_intros(1) split_list)
    
    have in_carrier: "u \<in> carrier R" "set Us \<subseteq> carrier R"
      using independent_in_carrier[OF Cons(2)] by auto 
    
    have "distinct Vs"
      using Cons(3-4) independent_distinct[OF Cons(2)]
      by (metis card_distinct distinct_card)
    hence "u \<notin> set (Vs' @ Vs'')" and "u \<notin> set Us"
      using independent_distinct[OF Cons(2)] unfolding Vs by auto
    hence set_eq: "set Us = set (Vs' @ Vs'')" and "length (Vs' @ Vs'') = length Us"
      using Cons(3-4) unfolding Vs by auto
    hence "independent K (Vs' @ Vs'')"
      using Cons(1)[OF independent_backwards(2)[OF Cons(2)]] unfolding Vs by simp
    hence "independent K (u # (Vs' @ Vs''))"
      using li_Cons Span_same_set[OF _ set_eq] independent_backwards(1)[OF Cons(2)] in_carrier by auto
    hence "independent K (Vs' @ (u # Vs''))"
      using independent_rotate1[of "u # Vs'" Vs''] by auto
    thus ?case unfolding Vs .
  qed
qed

lemma replacement_theorem:
  assumes "independent K (Us' @ Us)" and "independent K Vs"
    and "Span K (Us' @ Us) \<subseteq> Span K Vs"
  shows "\<exists>Vs'. set Vs' \<subseteq> set Vs \<and> length Vs' = length Us' \<and> independent K (Vs' @ Us)"
  using assms
proof (induct "length Us'" arbitrary: Us' Us)
  case 0 thus ?case by auto 
next
  case (Suc n)
  then obtain u Us'' where Us'': "Us' = Us'' @ [u]"
    by (metis list.size(3) nat.simps(3) rev_exhaust)
  then obtain Vs' where Vs': "set Vs' \<subseteq> set Vs" "length Vs' = n" "independent K (Vs' @ (u # Us))"
    using Suc(1)[of Us'' "u # Us"] Suc(2-5) by auto
  hence li: "independent K ((u # Vs') @ Us)"
    using independent_same_set[OF _ _ Vs'(3), of "(u # Vs') @ Us"] by auto
  moreover have in_carrier:
    "u \<in> carrier R" "set Us \<subseteq> carrier R" "set Us' \<subseteq> carrier R" "set Vs \<subseteq> carrier R"
    using Suc(3-4)[THEN independent_in_carrier] Us'' by auto
  moreover have "Span K ((u # Vs') @ Us) \<subseteq> Span K Vs"
  proof -
    have "set Us \<subseteq> Span K Vs" "u \<in> Span K Vs"
      using Suc(5) Span_base_incl[of "Us' @ Us"] Us'' in_carrier(2-3) by auto
    moreover have "set Vs' \<subseteq> Span K Vs"
      using Span_base_incl[OF in_carrier(4)] Vs'(1) by auto
    ultimately have "set ((u # Vs') @ Us) \<subseteq> Span K Vs" by auto
    thus ?thesis
      using mono_Span_subset[OF _ in_carrier(4)] by (simp del: Span.simps)
  qed
  ultimately obtain v where "v \<in> set Vs" "independent K ((v # Vs') @ Us)"
    using independent_replacement[OF _ Suc(4), of u "Vs' @ Us"] by auto
  thus ?case
    using Vs'(1-2) Suc(2)
    by (metis (mono_tags, lifting) insert_subset length_Cons list.simps(15))
qed

corollary independent_length_le:
  assumes "independent K Us" and "independent K Vs"
  shows "set Us \<subseteq> Span K Vs \<Longrightarrow> length Us \<le> length Vs"
proof -
  assume "set Us \<subseteq> Span K Vs"
  hence "Span K Us \<subseteq> Span K Vs"
    using mono_Span_subset[OF _ independent_in_carrier[OF assms(2)]] by simp
  then obtain Vs' where Vs': "set Vs' \<subseteq> set Vs" "length Vs' = length Us" "independent K Vs'"
    using replacement_theorem[OF _ assms(2), of Us "[]"] assms(1) by auto
  hence "card (set Vs') \<le> card (set Vs)"
    by (simp add: card_mono)
  thus "length Us \<le> length Vs"
    using independent_distinct assms(2) Vs'(2-3) by (simp add: distinct_card)
qed


subsection \<open>Dimension\<close>

lemma exists_base:
  assumes "dimension n K E"
  shows "\<exists>Vs. set Vs \<subseteq> carrier R \<and> independent K Vs \<and> length Vs = n \<and> Span K Vs = E"
    (is "\<exists>Vs. ?base K Vs E n")
  using assms
proof (induct E rule: dimension.induct)
  case zero_dim thus ?case by auto
next
  case (Suc_dim v E n K)
  then obtain Vs where Vs: "set Vs \<subseteq> carrier R" "independent K Vs" "length Vs = n" "Span K Vs = E"
    by auto
  hence "?base K (v # Vs) (line_extension K v E) (Suc n)"
    using Suc_dim li_Cons by auto
  thus ?case by blast
qed

lemma dimension_zero [intro]: "dimension 0 K E \<Longrightarrow> E = { \<zero> }"
proof -
  assume "dimension 0 K E"
  then obtain Vs where "length Vs = 0" "Span K Vs = E"
    using exists_base by blast
  thus ?thesis
    by auto
qed

lemma dimension_independent [intro]: "independent K Us \<Longrightarrow> dimension (length Us) K (Span K Us)"
proof (induct Us)
  case Nil thus ?case by simp
next
  case Cons thus ?case
    using Suc_dim[OF independent_backwards(3,1)[OF Cons(2)]] by auto
qed

lemma dimensionI:
  assumes "independent K Us" "Span K Us = E"
  shows "dimension (length Us) K E"
  using dimension_independent[OF assms(1)] assms(2) by simp

lemma space_subgroup_props:
  assumes "dimension n K E"
  shows "E \<subseteq> carrier R"
    and "\<zero> \<in> E"
    and "\<And>v1 v2. \<lbrakk> v1 \<in> E; v2 \<in> E \<rbrakk> \<Longrightarrow> (v1 \<oplus> v2) \<in> E"
    and "\<And>v. v \<in> E \<Longrightarrow> (\<ominus> v) \<in> E"
    and "\<And>k v. \<lbrakk> k \<in> K; v \<in> E \<rbrakk> \<Longrightarrow> k \<otimes> v \<in> E"
    and "\<lbrakk> k \<in> K - { \<zero> }; a \<in> carrier R \<rbrakk> \<Longrightarrow> k \<otimes> a \<in> E \<Longrightarrow> a \<in> E"
  using exists_base[OF assms] Span_subgroup_props Span_smult_closed Span_m_inv_simprule by auto

lemma independent_length_le_dimension:
  assumes "dimension n K E" and "independent K Us" "set Us \<subseteq> E"
  shows "length Us \<le> n"
proof -
  obtain Vs where Vs: "set Vs \<subseteq> carrier R" "independent K Vs" "length Vs = n" "Span K Vs = E"
    using exists_base[OF assms(1)] by auto
  thus ?thesis
    using independent_length_le assms(2-3) by auto
qed

lemma dimension_is_inj:
  assumes "dimension n K E" and "dimension m K E"
  shows "n = m"
proof -
  { fix n m assume n: "dimension n K E" and m: "dimension m K E"
    then obtain Vs
      where Vs: "set Vs \<subseteq> carrier R" "independent K Vs" "length Vs = n" "Span K Vs = E"
      using exists_base by meson
    hence "n \<le> m"
      using independent_length_le_dimension[OF m Vs(2)] Span_base_incl[OF Vs(1)] by auto
  } note aux_lemma = this

  show ?thesis
    using aux_lemma[OF assms] aux_lemma[OF assms(2,1)] by simp
qed

corollary independent_length_eq_dimension:
  assumes "dimension n K E" and "independent K Us" "set Us \<subseteq> E"
  shows "length Us = n \<longleftrightarrow> Span K Us = E"
proof
  assume len: "length Us = n" show "Span K Us = E"
  proof (rule ccontr)
    assume "Span K Us \<noteq> E"
    hence "Span K Us \<subset> E"
      using mono_Span_subset[of Us] exists_base[OF assms(1)] assms(3) by blast
    then obtain v where v: "v \<in> E" "v \<notin> Span K Us"
      using Span_strict_incl exists_base[OF assms(1)] space_subgroup_props(1)[OF assms(1)] assms by blast
    hence "independent K (v # Us)"
      using li_Cons[OF _ _ assms(2)] space_subgroup_props(1)[OF assms(1)] by auto
    hence "length (v # Us) \<le> n"
      using independent_length_le_dimension[OF assms(1)] v(1) assms(2-3) by fastforce
    moreover have "length (v # Us) = Suc n"
      using len by simp
    ultimately show False by simp
  qed
next
  assume "Span K Us = E"
  hence "dimension (length Us) K E"
    using dimensionI assms by auto
  thus "length Us = n"
    using dimension_is_inj[OF assms(1)] by auto
qed

lemma complete_base:
  assumes "dimension n K E" and "independent K Us" "set Us \<subseteq> E"
  shows "\<exists>Vs. length (Vs @ Us) = n \<and> independent K (Vs @ Us) \<and> Span K (Vs @ Us) = E"
proof -
  { fix Us k assume "k \<le> n" "independent K Us" "set Us \<subseteq> E" "length Us = k"
    hence "\<exists>Vs. length (Vs @ Us) = n \<and> independent K (Vs @ Us) \<and> Span K (Vs @ Us) = E"
    proof (induct arbitrary: Us rule: inc_induct)
      case base thus ?case
        using independent_length_eq_dimension[OF assms(1) base(1-2)] by auto
    next
      case (step m)
      have "Span K Us \<subseteq> E"
        using mono_Span_subset step(4-6) exists_base[OF assms(1)] by blast
      hence "Span K Us \<subset> E"
        using independent_length_eq_dimension[OF assms(1) step(4-5)] step(2,6) assms(1) by blast
      then obtain v where v: "v \<in> E" "v \<notin> Span K Us"
        using Span_strict_incl exists_base[OF assms(1)] by blast
      hence "independent K (v # Us)"
        using space_subgroup_props(1)[OF assms(1)] li_Cons[OF _ v(2) step(4)] by auto
      then obtain Vs
        where "length (Vs @ (v # Us)) = n" "independent K (Vs @ (v # Us))" "Span K (Vs @ (v # Us)) = E"
        using step(3)[of "v # Us"] step(1-2,4-6) v by auto 
      thus ?case
        by (metis append.assoc append_Cons append_Nil)  
    qed } note aux_lemma = this

  have "length Us \<le> n"
    using independent_length_le_dimension[OF assms] .
  thus ?thesis
    using aux_lemma[OF _ assms(2-3)] by auto
qed

lemma dimension_backwards:
  "dimension (Suc n) K E \<Longrightarrow> \<exists>v \<in> carrier R. \<exists>E'. dimension n K E' \<and> v \<notin> E' \<and> E = line_extension K v E'"
  by (cases rule: dimension.cases) (auto)

lemma dimension_direct_sum_space:
  assumes "dimension n K E" and "dimension m K F" and "E \<inter> F = { \<zero> }"
  shows "dimension (n + m) K (E <+>\<^bsub>R\<^esub> F)"
proof -
  obtain Us Vs
    where Vs: "set Vs \<subseteq> carrier R" "independent K Vs" "length Vs = n" "Span K Vs = E"
      and Us: "set Us \<subseteq> carrier R" "independent K Us" "length Us = m" "Span K Us = F"
    using assms(1-2)[THEN exists_base] by auto
  hence "Span K (Vs @ Us) = E <+>\<^bsub>R\<^esub> F"
    using Span_append_eq_set_add by auto
  moreover have "independent K (Vs @ Us)"
    using assms(3) independent_append[OF Vs(2) Us(2)] unfolding Vs(4) Us(4) by simp
  ultimately show "dimension (n + m) K (E <+>\<^bsub>R\<^esub> F)"
    using dimensionI[of "Vs @ Us"] Vs(3) Us(3) by auto
qed

lemma dimension_sum_space:
  assumes "dimension n K E" and "dimension m K F" and "dimension k K (E \<inter> F)"
  shows "dimension (n + m - k) K (E <+>\<^bsub>R\<^esub> F)"
proof -
  obtain Bs
    where Bs: "set Bs \<subseteq> carrier R" "length Bs = k" "independent K Bs" "Span K Bs = E \<inter> F"
    using exists_base[OF assms(3)] by blast
  then obtain Us Vs
    where Us: "length (Us @ Bs) = n" "independent K (Us @ Bs)" "Span K (Us @ Bs) = E"
      and Vs: "length (Vs @ Bs) = m" "independent K (Vs @ Bs)" "Span K (Vs @ Bs) = F"
    using Span_base_incl[OF Bs(1)] assms(1-2)[THEN complete_base] by (metis le_infE)
  hence in_carrier: "set Us \<subseteq> carrier R" "set (Vs @ Bs) \<subseteq> carrier R"
    using independent_in_carrier[OF Us(2)] independent_in_carrier[OF Vs(2)] by auto
  hence "Span K Us \<inter> (Span K (Vs @ Bs)) \<subseteq> Span K Bs"
    using Bs(4) Us(3) Vs(3) mono_Span_append(1)[OF _ Bs(1), of Us] by auto 
  hence "Span K Us \<inter> (Span K (Vs @ Bs)) \<subseteq> { \<zero> }"
    using independent_split(3)[OF Us(2)] by blast
  hence "Span K Us \<inter> (Span K (Vs @ Bs)) = { \<zero> }"
    using in_carrier[THEN Span_subgroup_props(2)] by auto

  hence dim: "dimension (n + m - k) K (Span K (Us @ (Vs @ Bs)))"
    using independent_append[OF independent_split(2)[OF Us(2)] Vs(2)] Us(1) Vs(1) Bs(2)
          dimension_independent[of "Us @ (Vs @ Bs)"] by auto

  have "(Span K Us) <+>\<^bsub>R\<^esub> F \<subseteq> E <+>\<^bsub>R\<^esub> F"
    using mono_Span_append(1)[OF in_carrier(1) Bs(1)] Us(3) unfolding set_add_def' by auto
  moreover have "E <+>\<^bsub>R\<^esub> F \<subseteq> (Span K Us) <+>\<^bsub>R\<^esub> F"
  proof
    fix v assume "v \<in> E <+>\<^bsub>R\<^esub> F"
    then obtain u' v' where v: "u' \<in> E" "v' \<in> F" "v = u' \<oplus> v'"
      unfolding set_add_def' by auto
    then obtain u1' u2' where u1': "u1' \<in> Span K Us" and u2': "u2' \<in> Span K Bs" and u': "u' = u1' \<oplus> u2'"
      using Span_append_eq_set_add[OF in_carrier(1) Bs(1)] Us(3) unfolding set_add_def' by blast

    have "v = u1' \<oplus> (u2' \<oplus> v')"
      using Span_subgroup_props(1)[OF Bs(1)] Span_subgroup_props(1)[OF in_carrier(1)]
            space_subgroup_props(1)[OF assms(2)] u' v u1' u2' a_assoc[of u1' u2' v'] by auto
    moreover have "u2' \<oplus> v' \<in> F"
      using space_subgroup_props(3)[OF assms(2) _ v(2)] u2' Bs(4) by auto
    ultimately show "v \<in> (Span K Us) <+>\<^bsub>R\<^esub> F"
      using u1' unfolding set_add_def' by auto
  qed
  ultimately have "Span K (Us @ (Vs @ Bs)) = E <+>\<^bsub>R\<^esub> F" 
    using Span_append_eq_set_add[OF in_carrier] Vs(3) by auto

  thus ?thesis using dim by simp
qed

end

end

lemma (in ring) telescopic_base_aux:
  assumes "subfield K R" "subfield F R"
    and "dimension n K F" and "dimension 1 F E"
  shows "dimension n K E"
proof -
  obtain Us u
    where Us: "set Us \<subseteq> carrier R" "length Us = n" "independent K Us" "Span K Us = F"
      and u: "u \<in> carrier R" "independent F [u]" "Span F [u] = E"
    using exists_base[OF assms(2,4)] exists_base[OF assms(1,3)] independent_backwards(3) assms(2)
    by (metis One_nat_def length_0_conv length_Suc_conv)
  have in_carrier: "set (map (\<lambda>u'. u' \<otimes> u) Us) \<subseteq> carrier R"
    using Us(1) u(1) by (induct Us) (auto)
  
  have li: "independent K (map (\<lambda>u'. u' \<otimes> u) Us)"
  proof (rule trivial_combine_imp_independent[OF assms(1) in_carrier])
    fix Ks assume Ks: "set Ks \<subseteq> K" and "combine Ks (map (\<lambda>u'. u' \<otimes> u) Us) = \<zero>"
    hence "(combine Ks Us) \<otimes> u = \<zero>"
      using combine_l_distr[OF _ Us(1) u(1)] subring_props(1)[OF assms(1)] by auto
    hence "combine [ combine Ks Us ] [ u ] = \<zero>"
      by simp
    moreover have "combine Ks Us \<in> F"
      using Us(4) Ks(1) Span_eq_combine_set[OF assms(1) Us(1)] by auto
    ultimately have "combine Ks Us = \<zero>"
      using independent_imp_trivial_combine[OF assms(2) u(2), of "[ combine Ks Us ]"] by auto
    hence "set (take (length Us) Ks) \<subseteq> { \<zero> }"
      using independent_imp_trivial_combine[OF assms(1) Us(3) Ks(1)] by simp
    thus "set (take (length (map (\<lambda>u'. u' \<otimes> u) Us)) Ks) \<subseteq> { \<zero> }" by simp
  qed

  have "E \<subseteq> Span K (map (\<lambda>u'. u' \<otimes> u) Us)"
  proof
    fix v assume "v \<in> E"
    then obtain f where f: "f \<in> F" "v = f \<otimes> u \<oplus> \<zero>"
      using u(1,3) line_extension_mem_iff[OF assms(2)] by auto
    then obtain Ks where Ks: "set Ks \<subseteq> K" "f = combine Ks Us"
      using Span_eq_combine_set[OF assms(1) Us(1)] Us(4) by auto
    have "v = f \<otimes> u"
      using subring_props(1)[OF assms(2)] f u(1) by auto
    hence "v = combine Ks (map (\<lambda>u'. u' \<otimes> u) Us)"
      using combine_l_distr[OF _ Us(1) u(1), of Ks] Ks(1-2)
            subring_props(1)[OF assms(1)] by blast
    thus "v \<in> Span K (map (\<lambda>u'. u' \<otimes> u) Us)"
      unfolding Span_eq_combine_set[OF assms(1) in_carrier] using Ks(1) by blast
  qed
  moreover have "Span K (map (\<lambda>u'. u' \<otimes> u) Us) \<subseteq> E"
  proof
    fix v assume "v \<in> Span K (map (\<lambda>u'. u' \<otimes> u) Us)"
    then obtain Ks where Ks: "set Ks \<subseteq> K" "v = combine Ks (map (\<lambda>u'. u' \<otimes> u) Us)"
      unfolding Span_eq_combine_set[OF assms(1) in_carrier] by blast
    hence "v = (combine Ks Us) \<otimes> u"
      using combine_l_distr[OF _ Us(1) u(1), of Ks] subring_props(1)[OF assms(1)] by auto
    moreover have "combine Ks Us \<in> F"
      using Us(4) Span_eq_combine_set[OF assms(1) Us(1)] Ks(1) by blast
    ultimately have "v = (combine Ks Us) \<otimes> u \<oplus> \<zero>" and "combine Ks Us \<in> F"
      using subring_props(1)[OF assms(2)] u(1) by auto
    thus "v \<in> E"
      using u(3) line_extension_mem_iff[OF assms(2)] by auto
  qed
  ultimately have "Span K (map (\<lambda>u'. u' \<otimes> u) Us) = E" by auto
  thus ?thesis
    using dimensionI[OF assms(1) li] Us(2) by simp
qed

lemma (in ring) telescopic_base:
  assumes "subfield K R" "subfield F R"
    and "dimension n K F" and "dimension m F E"
  shows "dimension (n * m) K E"
  using assms(4)
proof (induct m arbitrary: E)
  case 0 thus ?case
    using dimension_zero[OF assms(2)] zero_dim by auto
next
  case (Suc m)
  obtain Vs
    where Vs: "set Vs \<subseteq> carrier R" "length Vs = Suc m" "independent F Vs" "Span F Vs = E"
    using exists_base[OF assms(2) Suc(2)] by blast
  then obtain v Vs' where v: "Vs = v # Vs'"
    by (meson length_Suc_conv)
  hence li: "independent F [ v ]" "independent F Vs'" and inter: "Span F [ v ] \<inter> Span F Vs' = { \<zero> }"
    using Vs(3) independent_split[OF assms(2), of "[ v ]" Vs'] by auto
  have "dimension n K (Span F [ v ])"
    using dimension_independent[OF assms(2) li(1)] telescopic_base_aux[OF assms(1-3)] by simp
  moreover have "dimension (n * m) K (Span F Vs')"
    using Suc(1) dimension_independent[OF assms(2) li(2)] Vs(2) unfolding v by auto
  ultimately have "dimension (n * Suc m) K (Span F [ v ] <+>\<^bsub>R\<^esub> Span F Vs')"
    using dimension_direct_sum_space[OF assms(1) _ _ inter] by auto
  thus "dimension (n * Suc m) K E"
    using Span_append_eq_set_add[OF assms(2) li[THEN independent_in_carrier]] Vs(4) v by auto 
qed


(*
lemma combine_take:
  assumes "set Ks  \<subseteq> carrier R" "set Us \<subseteq> carrier R"
  shows "length Ks \<le> length Us \<Longrightarrow> combine Ks Us = combine Ks (take (length Ks) Us)"
    and "length Us \<le> length Ks \<Longrightarrow> combine Ks Us = combine (take (length Us) Ks) Us"
proof -
  assume len: "length Ks \<le> length Us"
  hence Us: "Us = (take (length Ks) Us) @ (drop (length Ks) Us)" by auto
  hence set_t: "set (take (length Ks) Us) \<subseteq> carrier R" and set_d: "set (drop (length Ks) Us) \<subseteq> carrier R"
    using assms(2) len by (metis le_sup_iff set_append)+
  hence "combine Ks Us = (combine Ks (take (length Ks) Us)) \<oplus> \<zero>"
    using combine_append[OF _ assms(1), of "take (length Ks) Us" "[]" "drop (length Ks) Us"] len by auto
  also have " ... = combine Ks (take (length Ks) Us)"
    using combine_in_carrier[OF assms(1) set_t] by auto
  finally show "combine Ks Us = combine Ks (take (length Ks) Us)" .
next
  assume len: "length Us \<le> length Ks"
  hence Us: "Ks = (take (length Us) Ks) @ (drop (length Us) Ks)" by auto
  hence set_t: "set (take (length Us) Ks) \<subseteq> carrier R" and set_d: "set (drop (length Us) Ks) \<subseteq> carrier R"
    using assms(1) len by (metis le_sup_iff set_append)+
  hence "combine Ks Us = (combine (take (length Us) Ks) Us) \<oplus> \<zero>"
    using combine_append[OF _ _ assms(2), of "take (length Us) Ks" "drop (length Us) Ks" "[]"] len by auto
  also have " ... = combine (take (length Us) Ks) Us"
    using combine_in_carrier[OF set_t assms(2)] by auto 
  finally show "combine Ks Us = combine (take (length Us) Ks) Us" .
qed
*)

(*
lemma combine_normalize:
  assumes "set Ks \<subseteq> K" "set Us \<subseteq> carrier R" "a = combine Ks Us" 
  shows "\<exists>Ks'. set Ks' \<subseteq> K \<and> length Ks' = length Us \<and> a = combine Ks' Us"
proof (cases "length Ks \<le> length Us")
  assume "\<not> length Ks \<le> length Us"
  hence len: "length Us < length Ks" by simp
  hence "length (take (length Us) Ks) = length Us" and "set (take (length Us) Ks) \<subseteq> K"
    using assms(1) by (auto, metis contra_subsetD in_set_takeD)
  thus ?thesis
    using combine_take(2)[OF _ assms(2), of Ks] assms(1,3) subring_props(1) len
    by (metis dual_order.trans nat_less_le)
next
  assume len: "length Ks \<le> length Us"
  have Ks: "set Ks \<subseteq> carrier R" and set_r: "set (replicate (length Us - length Ks) \<zero>) \<subseteq> carrier R"
    using assms subring_props(1) zero_closed by (metis dual_order.trans, auto) 
  moreover
  have set_t: "set (take (length Ks) Us) \<subseteq> carrier R"
   and set_d: "set (drop (length Ks) Us) \<subseteq> carrier R"
    using assms(2) len dual_order.trans by (metis set_take_subset, metis set_drop_subset)
  ultimately 
  have "combine (Ks @ (replicate (length Us - length Ks) \<zero>)) Us =
       (combine Ks (take (length Ks) Us)) \<oplus>
       (combine (replicate (length Us - length Ks) \<zero>) (drop (length Ks) Us))"
    using combine_append[OF _ Ks set_t set_r set_d] len by auto
  also have " ... = combine Ks (take (length Ks) Us)"
    using combine_replicate[OF set_d] combine_in_carrier[OF Ks set_t] by auto
  also have " ... = a"
    using combine_take(1)[OF Ks assms(2) len] assms(3) by simp
  finally have "combine (Ks @ (replicate (length Us - length Ks) \<zero>)) Us = a" .
  moreover have "set (Ks @ (replicate (length Us - length Ks) \<zero>)) \<subseteq> K"
    using assms(1) subring_props(2) by auto
  moreover have "length (Ks @ (replicate (length Us - length Ks) \<zero>)) = length Us"
    using len by simp
  ultimately show ?thesis by blast
qed
*)

end