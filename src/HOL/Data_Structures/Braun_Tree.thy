(* Author: Tobias Nipkow *)

section \<open>Braun Trees\<close>

theory Braun_Tree
imports "HOL-Library.Tree_Real"
begin

(* FIXME mv *)
lemma mod2_iff: "x mod 2 = (if even x then 0 else 1)"
by (simp add: odd_iff_mod_2_eq_one)
lemma Icc_eq_insert_lb_nat: "m \<le> n \<Longrightarrow> {m..n} = insert m {Suc m..n}"
by auto

text \<open>Braun Trees were studied by Braun and Rem~\cite{BraunRem}
and later Hoogerwoord~\cite{Hoogerwoord}.\<close>

fun braun :: "'a tree \<Rightarrow> bool" where
"braun Leaf = True" |
"braun (Node l x r) = ((size l = size r \<or> size l = size r + 1) \<and> braun l \<and> braun r)"

lemma braun_Node':
  "braun (Node l x r) = (size r \<le> size l \<and> size l \<le> size r + 1 \<and> braun l \<and> braun r)"
by auto

text \<open>The shape of a Braun-tree is uniquely determined by its size:\<close>

lemma braun_unique: "\<lbrakk> braun (t1::unit tree); braun t2; size t1 = size t2 \<rbrakk> \<Longrightarrow> t1 = t2"
proof (induction t1 arbitrary: t2)
  case Leaf thus ?case by simp
next
  case (Node l1 _ r1)
  from Node.prems(3) have "t2 \<noteq> Leaf" by auto
  then obtain l2 x2 r2 where [simp]: "t2 = Node l2 x2 r2" by (meson neq_Leaf_iff)
  with Node.prems have "size l1 = size l2 \<and> size r1 = size r2" by auto
  thus ?case using Node.prems(1,2) Node.IH by auto
qed

text \<open>Braun trees are balanced:\<close>

lemma balanced_if_braun: "braun t \<Longrightarrow> balanced t"
proof(induction t)
  case Leaf show ?case by (simp add: balanced_def)
next
  case (Node l x r)
  have "size l = size r \<or> size l = size r + 1" (is "?A \<or> ?B")
    using Node.prems by simp
  thus ?case
  proof
    assume "?A"
    thus ?thesis using Node
      apply(simp add: balanced_def min_def max_def)
      by (metis Node.IH balanced_optimal le_antisym le_refl)
  next
    assume "?B"
    thus ?thesis using Node by(intro balanced_Node_if_wbal1) auto
  qed
qed

subsection \<open>Numbering Nodes\<close>

text \<open>We show that a tree is a Braun tree iff a parity-based
numbering (\<open>braun_indices\<close>) of nodes yields an interval of numbers.\<close>

fun braun_indices :: "'a tree \<Rightarrow> nat set" where
"braun_indices Leaf = {}" |
"braun_indices (Node l _ r) = {1} \<union> (*) 2 ` braun_indices l \<union> Suc ` (*) 2 ` braun_indices r"

lemma braun_indices1: "0 \<notin> braun_indices t"
by (induction t) auto

lemma finite_braun_indices: "finite(braun_indices t)"
by (induction t) auto

lemma braun_indices_if_braun: "braun t \<Longrightarrow> braun_indices t = {1..size t}"
proof(induction t)
  case Leaf thus ?case by simp
next
  have *: "(*) 2 ` {a..b} \<union> Suc ` (*) 2 ` {a..b} = {2*a..2*b+1}" (is "?l = ?r") for a b
  proof
    show "?l \<subseteq> ?r" by auto
  next
    have "\<exists>x2\<in>{a..b}. x \<in> {Suc (2*x2), 2*x2}" if *: "x \<in> {2*a .. 2*b+1}" for x
    proof -
      have "x div 2 \<in> {a..b}" using * by auto
      moreover have "x \<in> {2 * (x div 2), Suc(2 * (x div 2))}" by auto
      ultimately show ?thesis by blast
    qed
    thus "?r \<subseteq> ?l" by fastforce
  qed
  case (Node l x r)
  hence "size l = size r \<or> size l = size r + 1" (is "?A \<or> ?B") by auto
  thus ?case
  proof
    assume ?A
    with Node show ?thesis by (auto simp: *)
  next
    assume ?B
    with Node show ?thesis by (auto simp: * atLeastAtMostSuc_conv)
  qed
qed

lemma disj_evens_odds: "(*) 2 ` A \<inter> Suc ` (*) 2 ` B = {}"
using double_not_eq_Suc_double by auto

lemma Suc0_notin_double: "Suc 0 \<notin> (*) 2 ` A"
by(auto)

lemma zero_in_double_iff: "(0::nat) \<in> (*) 2 ` A \<longleftrightarrow> 0 \<in> A"
by(auto)

lemma Suc_in_Suc_image_iff: "Suc n \<in> Suc ` A \<longleftrightarrow> n \<in> A"
by(auto)

lemmas nat_in_image = Suc0_notin_double zero_in_double_iff Suc_in_Suc_image_iff

lemma card_braun_indices: "card (braun_indices t) = size t"
proof (induction t)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case
    by(auto simp: UNION_singleton_eq_range finite_braun_indices card_Un_disjoint
                  card_insert_if disj_evens_odds card_image inj_on_def braun_indices1)
qed

lemma disj_union_eq_iff:
  "\<lbrakk> L1 \<inter> R2 = {}; L2 \<inter> R1 = {} \<rbrakk> \<Longrightarrow> L1 \<union> R1 = L2 \<union> R2 \<longleftrightarrow> L1 = L2 \<and> R1 = R2"
by blast

lemma inj_braun_indices: "braun_indices t1 = braun_indices t2 \<Longrightarrow> t1 = (t2::unit tree)"
proof(induction t1 arbitrary: t2)
  case Leaf thus ?case using braun_indices.elims by blast
next
  case (Node l1 x1 r1)
  have "t2 \<noteq> Leaf"
  proof
    assume "t2 = Leaf"
    with Node.prems show False by simp
  qed
  thus ?case using Node
    by (auto simp: neq_Leaf_iff insert_ident nat_in_image braun_indices1
                  disj_union_eq_iff disj_evens_odds inj_image_eq_iff inj_def)
qed

text \<open>How many even/odd natural numbers are there between m and n?\<close>

lemma card_atLeastAtMost_even:
  "card {i \<in> {m..n::nat}. even i} = (n+1-m + (m+1) mod 2) div 2" (is "?l m n = ?r m n")
proof(induction "n+1 - m" arbitrary: n m)
   case 0 thus ?case by simp
next
  case Suc
  have "m \<le> n" using Suc(2) by arith
  hence "{m..n} = insert m {m+1..n}" by auto
  hence "?l m n = card {i \<in> insert m {m+1..n}. even i}" by simp
  also have "\<dots> = ?r m n" (is "?l = ?r")
  proof (cases)
    assume "even m"
    hence "{i \<in> insert m {m+1..n}. even i} = insert m {i \<in> {m+1..n}. even i}" by auto
    hence "?l = card {i \<in> {m+1..n}. even i} + 1" by simp
    also have "\<dots> = (n-m + (m+2) mod 2) div 2 + 1" using Suc(1)[of n "m+1"] Suc(2) by simp
    also have "\<dots> = ?r" using \<open>even m\<close> \<open>m \<le> n\<close> by auto
    finally show ?thesis .
  next
    assume "odd m"
    hence "{i \<in> insert m {m+1..n}. even i} = {i \<in> {m+1..n}. even i}" by auto
    hence "?l = card ..." by simp
    also have "\<dots> = (n-m + (m+2) mod 2) div 2" using Suc(1)[of n "m+1"] Suc(2) by simp
    also have "\<dots> = ?r" using \<open>odd m\<close> \<open>m \<le> n\<close> even_iff_mod_2_eq_zero[of m] by simp
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma card_atLeastAtMost_odd: "card {i \<in> {m..n::nat}. odd i} = (n+1-m + m mod 2) div 2"
proof -
  let ?A = "{i \<in> {m..n}. odd i}"
  let ?B = "{i \<in> {m+1..n+1}. even i}"
  have "card ?A = card (Suc ` ?A)" by (simp add: card_image)
  also have "Suc ` ?A = ?B" using Suc_le_D by(force simp: image_iff)
  also have "card ?B = (n+1-m + (m) mod 2) div 2"
    using card_atLeastAtMost_even[of "m+1" "n+1"] by simp
  finally show ?thesis .
qed

lemma compact_ivl_even: assumes "A = {i \<in> {m..n}. even i}"
shows "A = (\<lambda>j. 2*(j-1) + m + m mod 2) ` {1..card A}" (is "_ = ?A")
proof
  let ?a = "(n+1-m + (m+1) mod 2) div 2"
  have "\<exists>j \<in> {1..?a}. i = 2*(j-1) + m + m mod 2" if *: "i \<in> {m..n}" "even i" for i
  proof -
    let ?j = "(i - (m + m mod 2)) div 2 + 1"
    have "?j \<in> {1..?a} \<and> i = 2*(?j-1) + m + m mod 2" using * by(auto simp: mod2_iff) presburger+
    thus ?thesis by blast
  qed
  thus "A \<subseteq> ?A" using assms
    by(auto simp: image_iff card_atLeastAtMost_even simp del: atLeastAtMost_iff)
next
  let ?a = "(n+1-m + (m+1) mod 2) div 2"
  have 1: "2 * (j - 1) + m + m mod 2 \<in> {m..n}" if *: "j \<in> {1..?a}" for j
    using * by(auto simp: mod2_iff)
  have 2: "even (2 * (j - 1) + m + m mod 2)" for j by presburger
  show "?A \<subseteq> A"
    apply(simp add: assms card_atLeastAtMost_even del: atLeastAtMost_iff One_nat_def)
    using 1 2 by blast
qed

lemma compact_ivl_odd:
  assumes "B = {i \<in> {m..n}. odd i}" shows "B = (\<lambda>i. 2*(i-1) + m + (m+1) mod 2) ` {1..card B}"
proof -
  define A :: " nat set" where "A = Suc ` B"
  have "A = {i \<in> {m+1..n+1}. even i}"
    using Suc_le_D by(force simp add: A_def assms image_iff)
  from compact_ivl_even[OF this]
  have "A = Suc ` (\<lambda>i. 2 * (i - 1) + m + (m + 1) mod 2) ` {1..card A}"
    by (simp add: image_comp o_def)
  hence B: "B = (\<lambda>i. 2 * (i - 1) + m + (m + 1) mod 2) ` {1..card A}"
    using A_def by (simp add: inj_image_eq_iff)
  have "card A = card B" by (metis A_def bij_betw_Suc bij_betw_same_card) 
  with B show ?thesis by simp
qed

lemma even_odd_decomp: assumes "\<forall>x \<in> A. even x" "\<forall>x \<in> B. odd x"  "A \<union> B = {m..n}"
shows "(let a = card A; b = card B in
   a + b = n+1-m \<and>
   A = (\<lambda>i. 2*(i-1) + m + m mod 2) ` {1..a} \<and>
   B = (\<lambda>i. 2*(i-1) + m + (m+1) mod 2) ` {1..b} \<and>
   (a = b \<or> a = b+1 \<and> even m \<or> a+1 = b \<and> odd m))"
proof -
  let ?a = "card A" let ?b = "card B"
  have "finite A \<and> finite B"
    by (metis \<open>A \<union> B = {m..n}\<close> finite_Un finite_atLeastAtMost)
  hence ab: "?a + ?b = Suc n - m"
    by (metis Int_emptyI assms card_Un_disjoint card_atLeastAtMost)
  have A: "A = {i \<in> {m..n}. even i}" using assms by auto
  hence A': "A = (\<lambda>i. 2*(i-1) + m + m mod 2) ` {1..?a}" by(rule compact_ivl_even)
  have B: "B = {i \<in> {m..n}. odd i}" using assms by auto
  hence B': "B = (\<lambda>i. 2*(i-1) + m + (m+1) mod 2) ` {1..?b}" by(rule compact_ivl_odd)
  have "?a = ?b \<or> ?a = ?b+1 \<and> even m \<or> ?a+1 = ?b \<and> odd m"
    apply(simp add: Let_def mod2_iff
      card_atLeastAtMost_even[of m n, simplified A[symmetric]]
      card_atLeastAtMost_odd[of m n, simplified B[symmetric]] split!: if_splits)
    by linarith
  with ab A' B' show ?thesis by simp
qed

lemma braun_if_braun_indices: "braun_indices t = {1..size t} \<Longrightarrow> braun t"
proof(induction t)
case Leaf
  then show ?case by simp
next
  case (Node t1 x2 t2)
  have 1: "i > 0 \<Longrightarrow> Suc(Suc(2 * (i - Suc 0))) = 2*i" for i::nat by(simp add: algebra_simps)
  have 2: "i > 0 \<Longrightarrow> 2 * (i - Suc 0) + 3 = 2*i + 1" for i::nat by(simp add: algebra_simps)
  have 3: "(*) 2 ` braun_indices t1 \<union> Suc ` (*) 2 ` braun_indices t2 =
     {2..size t1 + size t2 + 1}" using Node.prems
    by (simp add: insert_ident Icc_eq_insert_lb_nat nat_in_image braun_indices1)
  thus ?case using Node.IH even_odd_decomp[OF _ _ 3]
    by(simp add: card_image inj_on_def card_braun_indices Let_def 1 2 inj_image_eq_iff image_comp
           cong: image_cong_strong)
qed

lemma braun_iff_braun_indices: "braun t \<longleftrightarrow> braun_indices t = {1..size t}"
using braun_if_braun_indices braun_indices_if_braun by blast

end