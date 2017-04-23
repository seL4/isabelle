(*  Title:      HOL/Induct/Infinitely_Branching_Tree.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Infinitely branching trees\<close>

theory Infinitely_Branching_Tree
imports Main
begin

datatype 'a tree =
    Atom 'a
  | Branch "nat \<Rightarrow> 'a tree"

primrec map_tree :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b tree"
  where
    "map_tree f (Atom a) = Atom (f a)"
  | "map_tree f (Branch ts) = Branch (\<lambda>x. map_tree f (ts x))"

lemma tree_map_compose: "map_tree g (map_tree f t) = map_tree (g \<circ> f) t"
  by (induct t) simp_all

primrec exists_tree :: "('a \<Rightarrow> bool) \<Rightarrow> 'a tree \<Rightarrow> bool"
  where
    "exists_tree P (Atom a) = P a"
  | "exists_tree P (Branch ts) = (\<exists>x. exists_tree P (ts x))"

lemma exists_map:
  "(\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow>
    exists_tree P ts \<Longrightarrow> exists_tree Q (map_tree f ts)"
  by (induct ts) auto


subsection\<open>The Brouwer ordinals, as in ZF/Induct/Brouwer.thy.\<close>

datatype brouwer = Zero | Succ brouwer | Lim "nat \<Rightarrow> brouwer"

text \<open>Addition of ordinals\<close>
primrec add :: "brouwer \<Rightarrow> brouwer \<Rightarrow> brouwer"
  where
    "add i Zero = i"
  | "add i (Succ j) = Succ (add i j)"
  | "add i (Lim f) = Lim (\<lambda>n. add i (f n))"

lemma add_assoc: "add (add i j) k = add i (add j k)"
  by (induct k) auto

text \<open>Multiplication of ordinals\<close>
primrec mult :: "brouwer \<Rightarrow> brouwer \<Rightarrow> brouwer"
  where
    "mult i Zero = Zero"
  | "mult i (Succ j) = add (mult i j) i"
  | "mult i (Lim f) = Lim (\<lambda>n. mult i (f n))"

lemma add_mult_distrib: "mult i (add j k) = add (mult i j) (mult i k)"
  by (induct k) (auto simp add: add_assoc)

lemma mult_assoc: "mult (mult i j) k = mult i (mult j k)"
  by (induct k) (auto simp add: add_mult_distrib)

text \<open>We could probably instantiate some axiomatic type classes and use
  the standard infix operators.\<close>


subsection \<open>A WF Ordering for The Brouwer ordinals (Michael Compton)\<close>

text \<open>To use the function package we need an ordering on the Brouwer
  ordinals.  Start with a predecessor relation and form its transitive
  closure.\<close>

definition brouwer_pred :: "(brouwer \<times> brouwer) set"
  where "brouwer_pred = (\<Union>i. {(m, n). n = Succ m \<or> (\<exists>f. n = Lim f \<and> m = f i)})"

definition brouwer_order :: "(brouwer \<times> brouwer) set"
  where "brouwer_order = brouwer_pred\<^sup>+"

lemma wf_brouwer_pred: "wf brouwer_pred"
  unfolding wf_def brouwer_pred_def
  apply clarify
  apply (induct_tac x)
    apply blast+
  done

lemma wf_brouwer_order[simp]: "wf brouwer_order"
  unfolding brouwer_order_def
  by (rule wf_trancl[OF wf_brouwer_pred])

lemma [simp]: "(j, Succ j) \<in> brouwer_order"
  by (auto simp add: brouwer_order_def brouwer_pred_def)

lemma [simp]: "(f n, Lim f) \<in> brouwer_order"
  by (auto simp add: brouwer_order_def brouwer_pred_def)

text \<open>Example of a general function\<close>
function add2 :: "brouwer \<Rightarrow> brouwer \<Rightarrow> brouwer"
  where
    "add2 i Zero = i"
  | "add2 i (Succ j) = Succ (add2 i j)"
  | "add2 i (Lim f) = Lim (\<lambda>n. add2 i (f n))"
  by pat_completeness auto
termination
  by (relation "inv_image brouwer_order snd") auto

lemma add2_assoc: "add2 (add2 i j) k = add2 i (add2 j k)"
  by (induct k) auto

end
