(*  Title:      ZF/Induct/Binary_Trees.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header {* Binary trees *}

theory Binary_Trees imports Main begin

subsection {* Datatype definition *}

consts
  bt :: "i => i"

datatype "bt(A)" =
  Lf | Br ("a \<in> A", "t1 \<in> bt(A)", "t2 \<in> bt(A)")

declare bt.intros [simp]

lemma Br_neq_left: "l \<in> bt(A) ==> Br(x, l, r) \<noteq> l"
  by (induct arbitrary: x r set: bt) auto

lemma Br_iff: "Br(a, l, r) = Br(a', l', r') \<longleftrightarrow> a = a' & l = l' & r = r'"
  -- "Proving a freeness theorem."
  by (fast elim!: bt.free_elims)

inductive_cases BrE: "Br(a, l, r) \<in> bt(A)"
  -- "An elimination rule, for type-checking."

text {*
  \medskip Lemmas to justify using @{term bt} in other recursive type
  definitions.
*}

lemma bt_mono: "A \<subseteq> B ==> bt(A) \<subseteq> bt(B)"
  apply (unfold bt.defs)
  apply (rule lfp_mono)
    apply (rule bt.bnd_mono)+
  apply (rule univ_mono basic_monos | assumption)+
  done

lemma bt_univ: "bt(univ(A)) \<subseteq> univ(A)"
  apply (unfold bt.defs bt.con_defs)
  apply (rule lfp_lowerbound)
   apply (rule_tac [2] A_subset_univ [THEN univ_mono])
  apply (fast intro!: zero_in_univ Inl_in_univ Inr_in_univ Pair_in_univ)
  done

lemma bt_subset_univ: "A \<subseteq> univ(B) ==> bt(A) \<subseteq> univ(B)"
  apply (rule subset_trans)
   apply (erule bt_mono)
  apply (rule bt_univ)
  done

lemma bt_rec_type:
  "[| t \<in> bt(A);
    c \<in> C(Lf);
    !!x y z r s. [| x \<in> A;  y \<in> bt(A);  z \<in> bt(A);  r \<in> C(y);  s \<in> C(z) |] ==>
    h(x, y, z, r, s) \<in> C(Br(x, y, z))
  |] ==> bt_rec(c, h, t) \<in> C(t)"
  -- {* Type checking for recursor -- example only; not really needed. *}
  apply (induct_tac t)
   apply simp_all
  done


subsection {* Number of nodes, with an example of tail-recursion *}

consts  n_nodes :: "i => i"
primrec
  "n_nodes(Lf) = 0"
  "n_nodes(Br(a, l, r)) = succ(n_nodes(l) #+ n_nodes(r))"

lemma n_nodes_type [simp]: "t \<in> bt(A) ==> n_nodes(t) \<in> nat"
  by (induct set: bt) auto

consts  n_nodes_aux :: "i => i"
primrec
  "n_nodes_aux(Lf) = (\<lambda>k \<in> nat. k)"
  "n_nodes_aux(Br(a, l, r)) =
      (\<lambda>k \<in> nat. n_nodes_aux(r) `  (n_nodes_aux(l) ` succ(k)))"

lemma n_nodes_aux_eq:
    "t \<in> bt(A) ==> k \<in> nat ==> n_nodes_aux(t)`k = n_nodes(t) #+ k"
  apply (induct arbitrary: k set: bt)
   apply simp
  apply (atomize, simp)
  done

definition
  n_nodes_tail :: "i => i"  where
  "n_nodes_tail(t) == n_nodes_aux(t) ` 0"

lemma "t \<in> bt(A) ==> n_nodes_tail(t) = n_nodes(t)"
  by (simp add: n_nodes_tail_def n_nodes_aux_eq)


subsection {* Number of leaves *}

consts
  n_leaves :: "i => i"
primrec
  "n_leaves(Lf) = 1"
  "n_leaves(Br(a, l, r)) = n_leaves(l) #+ n_leaves(r)"

lemma n_leaves_type [simp]: "t \<in> bt(A) ==> n_leaves(t) \<in> nat"
  by (induct set: bt) auto


subsection {* Reflecting trees *}

consts
  bt_reflect :: "i => i"
primrec
  "bt_reflect(Lf) = Lf"
  "bt_reflect(Br(a, l, r)) = Br(a, bt_reflect(r), bt_reflect(l))"

lemma bt_reflect_type [simp]: "t \<in> bt(A) ==> bt_reflect(t) \<in> bt(A)"
  by (induct set: bt) auto

text {*
  \medskip Theorems about @{term n_leaves}.
*}

lemma n_leaves_reflect: "t \<in> bt(A) ==> n_leaves(bt_reflect(t)) = n_leaves(t)"
  by (induct set: bt) (simp_all add: add_commute)

lemma n_leaves_nodes: "t \<in> bt(A) ==> n_leaves(t) = succ(n_nodes(t))"
  by (induct set: bt) simp_all

text {*
  Theorems about @{term bt_reflect}.
*}

lemma bt_reflect_bt_reflect_ident: "t \<in> bt(A) ==> bt_reflect(bt_reflect(t)) = t"
  by (induct set: bt) simp_all

end
