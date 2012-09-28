(*  Title:      HOL/BNF/Examples/Infinite_Derivation_Trees/Tree.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Trees with nonterminal internal nodes and terminal leaves.
*)

header {* Trees with Nonterminal Internal Nodes and Terminal Leaves *}

theory Tree
imports Prelim
begin

hide_fact (open) Quotient_Product.prod_rel_def

typedecl N
typedecl T

codata Tree = NNode (root: N) (ccont: "(T + Tree) fset")


section {* Sugar notations for Tree *}

definition
"llift2 \<phi> as1 as2 \<longleftrightarrow>
 (\<forall> n. Inl n \<in> fset as1 \<longleftrightarrow> Inl n \<in> fset as2) \<and>
 (\<forall> tr1. Inr tr1 \<in> fset as1 \<longrightarrow> (\<exists> tr2. Inr tr2 \<in> fset as2 \<and> \<phi> tr1 tr2)) \<and>
 (\<forall> tr2. Inr tr2 \<in> fset as2 \<longrightarrow> (\<exists> tr1. Inr tr1 \<in> fset as1 \<and> \<phi> tr1 tr2))"

lemma pre_Tree_rel: "pre_Tree_rel \<phi> (n1,as1) (n2,as2) \<longleftrightarrow> n1 = n2 \<and> llift2 \<phi> as1 as2"
unfolding llift2_def pre_Tree_rel_def sum_rel_def[abs_def] prod_rel_def fset_rel_def split_conv
apply (auto split: sum.splits)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE sum.simps(1,2,4))
apply (metis sumE sum.simps(1,2,4))
done


subsection{* Coinduction *}

theorem Tree_coind_NNode[elim, consumes 1, case_names NNode, induct pred: "HOL.eq"]:
assumes phi: "\<phi> tr1 tr2" and
NNode: "\<And> n1 n2 as1 as2.
          \<lbrakk>\<phi> (NNode n1 as1) (NNode n2 as2)\<rbrakk> \<Longrightarrow>
          n1 = n2 \<and> llift2 \<phi> as1 as2"
shows "tr1 = tr2"
apply(rule mp[OF Tree.dtor_coinduct[of \<phi> tr1 tr2] phi]) proof clarify
  fix tr1 tr2  assume \<phi>: "\<phi> tr1 tr2"
  show "pre_Tree_rel \<phi> (Tree_dtor tr1) (Tree_dtor tr2)"
  apply(cases rule: Tree.ctor_exhaust[of tr1], cases rule: Tree.ctor_exhaust[of tr2])
  apply (simp add: Tree.dtor_ctor)
  apply(case_tac x, case_tac xa, simp)
  unfolding pre_Tree_rel apply(rule NNode) using \<phi> unfolding NNode_def by simp
qed

theorem TTree_coind[elim, consumes 1, case_names LLift]:
assumes phi: "\<phi> tr1 tr2" and
LLift: "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow> root tr1 = root tr2 \<and> llift2 \<phi> (ccont tr1) (ccont tr2)"
shows "tr1 = tr2"
using phi apply(induct rule: Tree_coind_NNode)
using LLift by (metis Tree.sels)


subsection{* The characteristic theorems transported from fset to set *}

definition "Node n as \<equiv> NNode n (the_inv fset as)"
definition "cont \<equiv> fset o ccont"
definition "unfold rt ct \<equiv> Tree_unfold rt (the_inv fset o ct)"
definition "corec rt ct \<equiv> Tree_corec rt (the_inv fset o ct)"

definition lift ("_ ^#" 200) where
"lift \<phi> as \<longleftrightarrow> (\<forall> tr. Inr tr \<in> as \<longrightarrow> \<phi> tr)"

definition lift2 ("_ ^#2" 200) where
"lift2 \<phi> as1 as2 \<longleftrightarrow>
 (\<forall> n. Inl n \<in> as1 \<longleftrightarrow> Inl n \<in> as2) \<and>
 (\<forall> tr1. Inr tr1 \<in> as1 \<longrightarrow> (\<exists> tr2. Inr tr2 \<in> as2 \<and> \<phi> tr1 tr2)) \<and>
 (\<forall> tr2. Inr tr2 \<in> as2 \<longrightarrow> (\<exists> tr1. Inr tr1 \<in> as1 \<and> \<phi> tr1 tr2))"

definition liftS ("_ ^#s" 200) where
"liftS trs = {as. Inr -` as \<subseteq> trs}"

lemma lift2_llift2:
"\<lbrakk>finite as1; finite as2\<rbrakk> \<Longrightarrow>
 lift2 \<phi> as1 as2 \<longleftrightarrow> llift2 \<phi> (the_inv fset as1) (the_inv fset as2)"
unfolding lift2_def llift2_def by auto

lemma llift2_lift2:
"llift2 \<phi> as1 as2 \<longleftrightarrow> lift2 \<phi> (fset as1) (fset as2)"
using lift2_llift2 by (metis finite_fset fset_cong fset_to_fset)

lemma mono_lift:
assumes "(\<phi>^#) as"
and "\<And> tr. \<phi> tr \<Longrightarrow> \<phi>' tr"
shows "(\<phi>'^#) as"
using assms unfolding lift_def[abs_def] by blast

lemma mono_liftS:
assumes "trs1 \<subseteq> trs2 "
shows "(trs1 ^#s) \<subseteq> (trs2 ^#s)"
using assms unfolding liftS_def[abs_def] by blast

lemma lift_mono:
assumes "\<phi> \<le> \<phi>'"
shows "(\<phi>^#) \<le> (\<phi>'^#)"
using assms unfolding lift_def[abs_def] by blast

lemma mono_lift2:
assumes "(\<phi>^#2) as1 as2"
and "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow> \<phi>' tr1 tr2"
shows "(\<phi>'^#2) as1 as2"
using assms unfolding lift2_def[abs_def] by blast

lemma lift2_mono:
assumes "\<phi> \<le> \<phi>'"
shows "(\<phi>^#2) \<le> (\<phi>'^#2)"
using assms unfolding lift2_def[abs_def] by blast

lemma finite_cont[simp]: "finite (cont tr)"
unfolding cont_def by auto

theorem Node_root_cont[simp]:
"Node (root tr) (cont tr) = tr"
using Tree.collapse unfolding Node_def cont_def
by (metis cont_def finite_cont fset_cong fset_to_fset o_def)

theorem Tree_simps[simp]:
assumes "finite as" and "finite as'"
shows "Node n as = Node n' as' \<longleftrightarrow> n = n' \<and> as = as'"
using assms Tree.inject unfolding Node_def
by (metis fset_to_fset)

theorem Tree_cases[elim, case_names Node Choice]:
assumes Node: "\<And> n as. \<lbrakk>finite as; tr = Node n as\<rbrakk> \<Longrightarrow> phi"
shows phi
apply(cases rule: Tree.exhaust[of tr])
using Node unfolding Node_def
by (metis Node Node_root_cont finite_cont)

theorem Tree_sel_ctor[simp]:
"root (Node n as) = n"
"finite as \<Longrightarrow> cont (Node n as) = as"
unfolding Node_def cont_def by auto

theorems root_Node = Tree_sel_ctor(1)
theorems cont_Node = Tree_sel_ctor(2)

theorem Tree_coind_Node[elim, consumes 1, case_names Node]:
assumes phi: "\<phi> tr1 tr2" and
Node:
"\<And> n1 n2 as1 as2.
   \<lbrakk>finite as1; finite as2; \<phi> (Node n1 as1) (Node n2 as2)\<rbrakk>
   \<Longrightarrow> n1 = n2 \<and> (\<phi>^#2) as1 as2"
shows "tr1 = tr2"
using phi apply(induct rule: Tree_coind_NNode)
unfolding llift2_lift2 apply(rule Node)
unfolding Node_def
apply (metis finite_fset)
apply (metis finite_fset)
by (metis finite_fset fset_cong fset_to_fset)

theorem Tree_coind[elim, consumes 1, case_names Lift, induct pred: "HOL.eq"]:
assumes phi: "\<phi> tr1 tr2" and
Lift: "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow>
                  root tr1 = root tr2 \<and> (\<phi>^#2) (cont tr1) (cont tr2)"
shows "tr1 = tr2"
using phi apply(induct rule: TTree_coind)
unfolding llift2_lift2 apply(rule Lift[unfolded cont_def comp_def]) .

theorem unfold:
"root (unfold rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (unfold rt ct b) = image (id \<oplus> unfold rt ct) (ct b)"
using Tree.sel_unfold[of rt "the_inv fset \<circ> ct" b] unfolding unfold_def
apply - apply metis
unfolding cont_def comp_def
by (metis (no_types) fset_to_fset map_fset_image)

theorem corec:
"root (corec rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (corec rt ct b) = image (id \<oplus> ([[id, corec rt ct]])) (ct b)"
using Tree.sel_corec[of rt "the_inv fset \<circ> ct" b] unfolding corec_def
apply -
apply simp
unfolding cont_def comp_def id_def
by (metis (no_types) fset_to_fset map_fset_image)

end
