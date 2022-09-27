(*  Title:      ZF/Induct/Binary_Trees.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>Binary trees\<close>

theory Binary_Trees imports ZF begin

subsection \<open>Datatype definition\<close>

consts
  bt :: "i \<Rightarrow> i"

datatype "bt(A)" =
  Lf | Br ("a \<in> A", "t1 \<in> bt(A)", "t2 \<in> bt(A)")

declare bt.intros [simp]

lemma Br_neq_left: "l \<in> bt(A) \<Longrightarrow> Br(x, l, r) \<noteq> l"
  by (induct arbitrary: x r set: bt) auto

lemma Br_iff: "Br(a, l, r) = Br(a', l', r') \<longleftrightarrow> a = a' \<and> l = l' \<and> r = r'"
  \<comment> \<open>Proving a freeness theorem.\<close>
  by (fast elim!: bt.free_elims)

inductive_cases BrE: "Br(a, l, r) \<in> bt(A)"
  \<comment> \<open>An elimination rule, for type-checking.\<close>

text \<open>
  \medskip Lemmas to justify using \<^term>\<open>bt\<close> in other recursive type
  definitions.
\<close>

lemma bt_mono: "A \<subseteq> B \<Longrightarrow> bt(A) \<subseteq> bt(B)"
    unfolding bt.defs
  apply (rule lfp_mono)
    apply (rule bt.bnd_mono)+
  apply (rule univ_mono basic_monos | assumption)+
  done

lemma bt_univ: "bt(univ(A)) \<subseteq> univ(A)"
    unfolding bt.defs bt.con_defs
  apply (rule lfp_lowerbound)
   apply (rule_tac [2] A_subset_univ [THEN univ_mono])
  apply (fast intro!: zero_in_univ Inl_in_univ Inr_in_univ Pair_in_univ)
  done

lemma bt_subset_univ: "A \<subseteq> univ(B) \<Longrightarrow> bt(A) \<subseteq> univ(B)"
  apply (rule subset_trans)
   apply (erule bt_mono)
  apply (rule bt_univ)
  done

lemma bt_rec_type:
  "\<lbrakk>t \<in> bt(A);
    c \<in> C(Lf);
    \<And>x y z r s. \<lbrakk>x \<in> A;  y \<in> bt(A);  z \<in> bt(A);  r \<in> C(y);  s \<in> C(z)\<rbrakk> \<Longrightarrow>
    h(x, y, z, r, s) \<in> C(Br(x, y, z))
\<rbrakk> \<Longrightarrow> bt_rec(c, h, t) \<in> C(t)"
  \<comment> \<open>Type checking for recursor -- example only; not really needed.\<close>
  apply (induct_tac t)
   apply simp_all
  done


subsection \<open>Number of nodes, with an example of tail-recursion\<close>

consts  n_nodes :: "i \<Rightarrow> i"
primrec
  "n_nodes(Lf) = 0"
  "n_nodes(Br(a, l, r)) = succ(n_nodes(l) #+ n_nodes(r))"

lemma n_nodes_type [simp]: "t \<in> bt(A) \<Longrightarrow> n_nodes(t) \<in> nat"
  by (induct set: bt) auto

consts  n_nodes_aux :: "i \<Rightarrow> i"
primrec
  "n_nodes_aux(Lf) = (\<lambda>k \<in> nat. k)"
  "n_nodes_aux(Br(a, l, r)) =
      (\<lambda>k \<in> nat. n_nodes_aux(r) `  (n_nodes_aux(l) ` succ(k)))"

lemma n_nodes_aux_eq:
    "t \<in> bt(A) \<Longrightarrow> k \<in> nat \<Longrightarrow> n_nodes_aux(t)`k = n_nodes(t) #+ k"
  apply (induct arbitrary: k set: bt)
   apply simp
  apply (atomize, simp)
  done

definition
  n_nodes_tail :: "i \<Rightarrow> i"  where
  "n_nodes_tail(t) \<equiv> n_nodes_aux(t) ` 0"

lemma "t \<in> bt(A) \<Longrightarrow> n_nodes_tail(t) = n_nodes(t)"
  by (simp add: n_nodes_tail_def n_nodes_aux_eq)


subsection \<open>Number of leaves\<close>

consts
  n_leaves :: "i \<Rightarrow> i"
primrec
  "n_leaves(Lf) = 1"
  "n_leaves(Br(a, l, r)) = n_leaves(l) #+ n_leaves(r)"

lemma n_leaves_type [simp]: "t \<in> bt(A) \<Longrightarrow> n_leaves(t) \<in> nat"
  by (induct set: bt) auto


subsection \<open>Reflecting trees\<close>

consts
  bt_reflect :: "i \<Rightarrow> i"
primrec
  "bt_reflect(Lf) = Lf"
  "bt_reflect(Br(a, l, r)) = Br(a, bt_reflect(r), bt_reflect(l))"

lemma bt_reflect_type [simp]: "t \<in> bt(A) \<Longrightarrow> bt_reflect(t) \<in> bt(A)"
  by (induct set: bt) auto

text \<open>
  \medskip Theorems about \<^term>\<open>n_leaves\<close>.
\<close>

lemma n_leaves_reflect: "t \<in> bt(A) \<Longrightarrow> n_leaves(bt_reflect(t)) = n_leaves(t)"
  by (induct set: bt) (simp_all add: add_commute)

lemma n_leaves_nodes: "t \<in> bt(A) \<Longrightarrow> n_leaves(t) = succ(n_nodes(t))"
  by (induct set: bt) simp_all

text \<open>
  Theorems about \<^term>\<open>bt_reflect\<close>.
\<close>

lemma bt_reflect_bt_reflect_ident: "t \<in> bt(A) \<Longrightarrow> bt_reflect(bt_reflect(t)) = t"
  by (induct set: bt) simp_all

end
