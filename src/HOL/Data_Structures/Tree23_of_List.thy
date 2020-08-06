(* Author: Tobias Nipkow *)

section \<open>2-3 Tree from List\<close>

theory Tree23_of_List
imports Tree23
begin

text \<open>Linear-time bottom up conversion of a list of items into a complete 2-3 tree
whose inorder traversal yields the list of items.\<close>


subsection "Code"

text \<open>Nonempty lists of 2-3 trees alternating with items, starting and ending with a 2-3 tree:\<close>

datatype 'a tree23s = T "'a tree23" | TTs "'a tree23" "'a" "'a tree23s"

abbreviation "not_T ts == (\<forall>t. ts \<noteq> T t)"

fun len :: "'a tree23s \<Rightarrow> nat" where
"len (T _) = 1" |
"len (TTs _ _ ts) = len ts + 1"

fun trees :: "'a tree23s \<Rightarrow> 'a tree23 set" where
"trees (T t) = {t}" |
"trees (TTs t a ts) = {t} \<union> trees ts"

text \<open>Join pairs of adjacent trees:\<close>

fun join_adj :: "'a tree23s \<Rightarrow> 'a tree23s" where
"join_adj (TTs t1 a (T t2)) = T(Node2 t1 a t2)" |
"join_adj (TTs t1 a (TTs t2 b (T t3))) = T(Node3 t1 a t2 b t3)" |
"join_adj (TTs t1 a (TTs t2 b tas)) = TTs (Node2 t1 a t2) b (join_adj tas)"

text \<open>Towards termination of \<open>join_all\<close>:\<close>

lemma len_ge2:
  "not_T ts \<Longrightarrow> len ts \<ge> 2"
by(cases ts rule: join_adj.cases) auto

lemma [measure_function]: "is_measure len"
by(rule is_measure_trivial)

lemma len_join_adj_div2:
  "not_T ts \<Longrightarrow> len(join_adj ts) \<le> len ts div 2"
by(induction ts rule: join_adj.induct) auto

lemma len_join_adj1: "not_T ts \<Longrightarrow> len(join_adj ts) < len ts"
using len_join_adj_div2[of ts] len_ge2[of ts] by simp

corollary len_join_adj2[termination_simp]: "len(join_adj (TTs t a ts)) \<le> len ts"
using len_join_adj1[of "TTs t a ts"] by simp

fun join_all :: "'a tree23s \<Rightarrow> 'a tree23" where
"join_all (T t) = t" |
"join_all tas = join_all (join_adj tas)"

fun leaves :: "'a list \<Rightarrow> 'a tree23s" where
"leaves [] = T Leaf" |
"leaves (a # as) = TTs Leaf a (leaves as)"

definition tree23_of_list :: "'a list \<Rightarrow> 'a tree23" where
"tree23_of_list as = join_all(leaves as)"


subsection \<open>Functional correctness\<close>

subsubsection \<open>\<open>inorder\<close>:\<close>

fun inorder2 :: "'a tree23s \<Rightarrow> 'a list" where
"inorder2 (T t) = inorder t" |
"inorder2 (TTs t a ts) = inorder t @ a # inorder2 ts"

lemma inorder2_join_adj: "not_T ts \<Longrightarrow> inorder2(join_adj ts) = inorder2 ts"
by (induction ts rule: join_adj.induct) auto

lemma inorder_join_all: "inorder (join_all ts) = inorder2 ts"
proof (induction ts rule: measure_induct_rule[where f = "len"])
  case (less ts)
  show ?case
  proof (cases ts)
    case T thus ?thesis by simp
  next
    case (TTs t a ts)
    then show ?thesis using less inorder2_join_adj[of "TTs t a ts"]
      by (simp add: le_imp_less_Suc len_join_adj2)
  qed
qed

lemma inorder2_leaves: "inorder2(leaves as) = as"
by(induction as) auto

lemma "inorder(tree23_of_list as) = as"
by(simp add: tree23_of_list_def inorder_join_all inorder2_leaves)

subsubsection \<open>Completeness:\<close>

lemma complete_join_adj:
  "\<forall>t \<in> trees ts. complete t \<and> height t = n \<Longrightarrow> not_T ts \<Longrightarrow>
   \<forall>t \<in> trees (join_adj ts). complete t \<and> height t = Suc n"
by (induction ts rule: join_adj.induct) auto

lemma complete_join_all:
 "\<forall>t \<in> trees ts. complete t \<and> height t = n \<Longrightarrow> complete (join_all ts)"
proof (induction ts arbitrary: n rule: measure_induct_rule[where f = "len"])
  case (less ts)
  show ?case
  proof (cases ts)
    case T thus ?thesis using less.prems by simp
  next
    case (TTs t a ts)
    then show ?thesis
      using less.prems apply simp
      using complete_join_adj[of "TTs t a ts" n, simplified] less.IH len_join_adj1 by blast
  qed
qed

lemma complete_leaves: "t \<in> trees (leaves as) \<Longrightarrow> complete t \<and> height t = 0"
by (induction as) auto

corollary complete: "complete(tree23_of_list as)"
by(simp add: tree23_of_list_def complete_leaves complete_join_all[of _ 0])


subsection "Linear running time"

fun t_join_adj :: "'a tree23s \<Rightarrow> nat" where
"t_join_adj (TTs t1 a (T t2)) = 1" |
"t_join_adj (TTs t1 a (TTs t2 b (T t3))) = 1" |
"t_join_adj (TTs t1 a (TTs t2 b ts)) = t_join_adj ts + 1"

fun t_join_all :: "'a tree23s \<Rightarrow> nat" where
"t_join_all (T t) = 1" |
"t_join_all ts = t_join_adj ts + t_join_all (join_adj ts)"

fun t_leaves :: "'a list \<Rightarrow> nat" where
"t_leaves [] = 1" |
"t_leaves (a # as) = t_leaves as + 1"

definition t_tree23_of_list :: "'a list \<Rightarrow> nat" where
"t_tree23_of_list as = t_leaves as + t_join_all(leaves as)"

lemma t_join_adj: "not_T ts \<Longrightarrow> t_join_adj ts \<le> len ts div 2"
by(induction ts rule: t_join_adj.induct) auto

lemma t_join_all: "t_join_all ts \<le> len ts"
proof(induction ts rule: measure_induct_rule[where f = len])
  case (less ts)
  show ?case
  proof (cases ts)
    case T thus ?thesis by simp
  next
    case TTs
    have 0: "\<forall>t. ts \<noteq> T t" using TTs by simp
    have "t_join_all ts = t_join_adj ts + t_join_all (join_adj ts)"
      using TTs by simp
    also have "\<dots> \<le> len ts div 2 + t_join_all (join_adj ts)"
      using t_join_adj[OF 0] by linarith
    also have "\<dots> \<le> len ts div 2 + len (join_adj ts)"
      using less.IH[of "join_adj ts"] len_join_adj1[OF 0] by simp
    also have "\<dots> \<le> len ts div 2 + len ts div 2"
      using len_join_adj_div2[OF 0] by linarith
    also have "\<dots> \<le> len ts" by linarith
    finally show ?thesis .
  qed
qed

lemma t_leaves: "t_leaves as = length as + 1"
by(induction as) auto

lemma len_leaves: "len(leaves as) = length as + 1"
by(induction as) auto

lemma t_tree23_of_list: "t_tree23_of_list as \<le> 2*(length as + 1)"
using t_join_all[of "leaves as"] by(simp add: t_tree23_of_list_def t_leaves len_leaves)

end
