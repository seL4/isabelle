(* Author: Tobias Nipkow *)

section \<open>Braun Trees\<close>

theory Braun_Tree
  imports "HOL-Library.Tree_Real"
begin

text \<open>Braun Trees were studied by Braun and Rem~\<^cite>\<open>"BraunRem"\<close>
and later Hoogerwoord~\<^cite>\<open>"Hoogerwoord"\<close>.\<close>

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

text \<open>Braun trees are almost complete:\<close>

lemma acomplete_if_braun: "braun t \<Longrightarrow> acomplete t"
proof(induction t)
  case Leaf show ?case by (simp add: acomplete_def)
next
  case (Node l x r) thus ?case using acomplete_Node_if_wbal2 by force
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

text "One direction:"

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

text "The other direction is more complicated. The following proof is due to Thomas Sewell."

lemma disj_evens_odds: "(*) 2 ` A \<inter> Suc ` (*) 2 ` B = {}"
  using double_not_eq_Suc_double by auto

lemma card_braun_indices: "card (braun_indices t) = size t"
proof (induction t)
  case Leaf thus ?case by simp
next
  case Node
  thus ?case
    by(auto simp: UNION_singleton_eq_range finite_braun_indices card_Un_disjoint
        card_insert_if disj_evens_odds card_image inj_on_def braun_indices1)
qed

lemma braun_indices_intvl_base_1:
  assumes bi: "braun_indices t = {m..n}"
  shows "{m..n} = {1..size t}"
proof (cases "t = Leaf")
  case True then show ?thesis using bi by simp
next
  case False
  note eqs = eqset_imp_iff[OF bi]
  from eqs[of 0] have 0: "0 < m"
    by (simp add: braun_indices1)
  from eqs[of 1] have 1: "m \<le> 1"
    by (cases t; simp add: False)
  from 0 1 have eq1: "m = 1" by simp
  from card_braun_indices[of t] show ?thesis
    by (simp add: bi eq1)
qed

lemma even_of_intvl_intvl:
  fixes S :: "nat set"
  assumes "S = {m..n} \<inter> {i. even i}"
  shows "\<exists>m' n'. S = (\<lambda>i. i * 2) ` {m'..n'}"
proof -
  have "S = (\<lambda>i. i * 2) ` {Suc m div 2..n div 2}"
    by (fastforce simp add: assms mult.commute)
  then show ?thesis
    by blast
qed

lemma odd_of_intvl_intvl:
  fixes S :: "nat set"
  assumes "S = {m..n} \<inter> {i. odd i}"
  shows "\<exists>m' n'. S = Suc ` (\<lambda>i. i * 2) ` {m'..n'}"
proof -
  have "S = Suc ` ({if n = 0 then 1 else m - 1..n - 1} \<inter> Collect even)"
    by (auto simp: assms image_def elim!: oddE)
  thus ?thesis
    by (metis even_of_intvl_intvl)
qed

lemma image_int_eq_image:
  "(\<forall>i \<in> S. f i \<in> T) \<Longrightarrow> (f ` S) \<inter> T = f ` S"
  "(\<forall>i \<in> S. f i \<notin> T) \<Longrightarrow> (f ` S) \<inter> T = {}"
  by auto

lemma braun_indices1_le:
  "i \<in> braun_indices t \<Longrightarrow> Suc 0 \<le> i"
  using braun_indices1 not_less_eq_eq by blast

lemma braun_if_braun_indices: "braun_indices t = {1..size t} \<Longrightarrow> braun t"
proof(induction t)
  case Leaf
  then show ?case by simp
next
  case (Node l x r)
  obtain t where t: "t = Node l x r" by simp
  then have "insert (Suc 0) ((*) 2 ` braun_indices l \<union> Suc ` (*) 2 ` braun_indices r) \<inter> {2..} 
           = {Suc 0..Suc (size l + size r)} \<inter> {2..}"
    by (metis Node.prems One_nat_def Suc_eq_plus1 Un_insert_left braun_indices.simps(2)
        sup_bot_left tree.size(4))
  then have eq: "{2 .. size t} = (\<lambda>i. i * 2) ` braun_indices l \<union> Suc ` (\<lambda>i. i * 2) ` braun_indices r"
    (is "?R = ?S \<union> ?T")
    by (simp add: t mult.commute Int_Un_distrib2 image_int_eq_image braun_indices1_le)
  then have ST: "?S = ?R \<inter> {i. even i}" "?T = ?R \<inter> {i. odd i}"
    by (simp_all add: Int_Un_distrib2 image_int_eq_image)
  from ST have l: "braun_indices l = {1 .. size l}"
    by (fastforce dest: braun_indices_intvl_base_1 dest!: even_of_intvl_intvl
        simp: mult.commute inj_image_eq_iff[OF inj_onI])
  from ST have r: "braun_indices r = {1 .. size r}"
    by (fastforce dest: braun_indices_intvl_base_1 dest!: odd_of_intvl_intvl
        simp: mult.commute inj_image_eq_iff[OF inj_onI])
  note STa = ST[THEN eqset_imp_iff, THEN iffD2]
  note STb = STa[of "size t"] STa[of "size t - 1"]
  then have "size l = size r \<or> size l = size r + 1"
    using t l r  by atomize auto
  with l r show ?case
    by (clarsimp simp: Node.IH)
qed

lemma braun_iff_braun_indices: "braun t \<longleftrightarrow> braun_indices t = {1..size t}"
  using braun_if_braun_indices braun_indices_if_braun by blast

end