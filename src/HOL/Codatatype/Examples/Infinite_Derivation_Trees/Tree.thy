(*  Title:      HOL/Codatatype/Examples/Infinite_Derivation_Trees/Tree.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Trees with nonterminal internal nodes and terminal leafs.
*)

header {* Trees with nonterminal internal nodes and terminal leafs *}

theory Tree
imports Prelim
begin

hide_fact (open) Quotient_Product.prod_pred_def

typedecl N  typedecl T

codata_raw Tree: 'Tree = "N \<times> (T + 'Tree) fset"


section {* Sugar notations for Tree *}

subsection{* Setup for map, set, pred *}

(* These should be eventually inferred from compositionality *)

lemma pre_Tree_map:
"pre_Tree_map f (n, as) = (n, map_fset (id \<oplus> f) as)"
unfolding pre_Tree_map_def id_apply
sum_map_def by simp

lemma pre_Tree_map':
"pre_Tree_map f n_as = (fst n_as, map_fset (id \<oplus> f) (snd n_as))"
using pre_Tree_map by(cases n_as, simp)


definition
"llift2 \<phi> as1 as2 \<longleftrightarrow>
 (\<forall> n. Inl n \<in> fset as1 \<longleftrightarrow> Inl n \<in> fset as2) \<and>
 (\<forall> tr1. Inr tr1 \<in> fset as1 \<longrightarrow> (\<exists> tr2. Inr tr2 \<in> fset as2 \<and> \<phi> tr1 tr2)) \<and>
 (\<forall> tr2. Inr tr2 \<in> fset as2 \<longrightarrow> (\<exists> tr1. Inr tr1 \<in> fset as1 \<and> \<phi> tr1 tr2))"

lemma pre_Tree_pred: "pre_Tree_pred \<phi> (n1,as1) (n2,as2) \<longleftrightarrow> n1 = n2 \<and> llift2 \<phi> as1 as2"
unfolding llift2_def pre_Tree_pred_def sum_pred_def[abs_def] prod_pred_def fset_pred_def split_conv
apply (auto split: sum.splits)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE)
apply (metis sumE sum.simps(1,2,4))
apply (metis sumE sum.simps(1,2,4))
done


subsection{* Constructors *}

definition NNode :: "N \<Rightarrow> (T + Tree)fset \<Rightarrow> Tree"
where "NNode n as \<equiv> Tree_fld (n,as)"

lemmas ctor_defs = NNode_def


subsection {* Pre-selectors *}

(* These are mere auxiliaries *)

definition "asNNode tr \<equiv> SOME n_as. NNode (fst n_as) (snd n_as) = tr"
lemmas pre_sel_defs = asNNode_def


subsection {* Selectors *}

(* One for each pair (constructor, constructor argument) *)

(* For NNode: *)
definition root :: "Tree \<Rightarrow> N" where "root tr = fst (asNNode tr)"
definition ccont :: "Tree \<Rightarrow> (T + Tree)fset" where "ccont tr = snd (asNNode tr)"

lemmas sel_defs = root_def ccont_def


subsection {* Basic properties *}

(* Constructors versus selectors *)
lemma NNode_surj: "\<exists> n as. NNode n as = tr"
unfolding NNode_def
by (metis Tree.fld_unf pair_collapse)

lemma NNode_asNNode:
"NNode (fst (asNNode tr)) (snd (asNNode tr)) = tr"
proof-
  obtain n as where "NNode n as = tr" using NNode_surj[of tr] by blast
  hence "NNode (fst (n,as)) (snd (n,as)) = tr" by simp
  thus ?thesis unfolding asNNode_def by(rule someI)
qed

theorem NNode_root_ccont[simp]:
"NNode (root tr) (ccont tr) = tr"
using NNode_asNNode unfolding root_def ccont_def .

(* Constructors *)
theorem TTree_simps[simp]:
"NNode n as = NNode n' as' \<longleftrightarrow> n = n' \<and> as = as'"
unfolding ctor_defs Tree.fld_inject by auto

theorem TTree_cases[elim, case_names NNode Choice]:
assumes NNode: "\<And> n as. tr = NNode n as \<Longrightarrow> phi"
shows phi
proof(cases rule: Tree.fld_exhaust[of tr])
  fix x assume "tr = Tree_fld x"
  thus ?thesis
  apply(cases x)
    using NNode unfolding ctor_defs apply blast
  done
qed

(* Constructors versus selectors *)
theorem TTree_sel_ctor[simp]:
"root (NNode n as) = n"
"ccont (NNode n as) = as"
unfolding root_def ccont_def
by (metis (no_types) NNode_asNNode TTree_simps)+


subsection{* Coinduction *}

theorem TTree_coind_Node[elim, consumes 1, case_names NNode, induct pred: "HOL.eq"]:
assumes phi: "\<phi> tr1 tr2" and
NNode: "\<And> n1 n2 as1 as2.
          \<lbrakk>\<phi> (NNode n1 as1) (NNode n2 as2)\<rbrakk> \<Longrightarrow>
          n1 = n2 \<and> llift2 \<phi> as1 as2"
shows "tr1 = tr2"
apply(rule mp[OF Tree.pred_coinduct[of \<phi> tr1 tr2] phi]) proof clarify
  fix tr1 tr2  assume \<phi>: "\<phi> tr1 tr2"
  show "pre_Tree_pred \<phi> (Tree_unf tr1) (Tree_unf tr2)"
  apply(cases rule: Tree.fld_exhaust[of tr1], cases rule: Tree.fld_exhaust[of tr2])
  apply (simp add: Tree.unf_fld)
  apply(case_tac x, case_tac xa, simp)
  unfolding pre_Tree_pred apply(rule NNode) using \<phi> unfolding NNode_def by simp
qed

theorem TTree_coind[elim, consumes 1, case_names LLift]:
assumes phi: "\<phi> tr1 tr2" and
LLift: "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow>
                   root tr1 = root tr2 \<and> llift2 \<phi> (ccont tr1) (ccont tr2)"
shows "tr1 = tr2"
using phi apply(induct rule: TTree_coind_Node)
using LLift by (metis TTree_sel_ctor)



subsection {* Coiteration *}

(* Preliminaries: *)
declare Tree.unf_fld[simp]
declare Tree.fld_unf[simp]

lemma Tree_unf_NNode[simp]:
"Tree_unf (NNode n as) = (n,as)"
unfolding NNode_def Tree.unf_fld ..

lemma Tree_unf_root_ccont:
"Tree_unf tr = (root tr, ccont tr)"
unfolding root_def ccont_def
by (metis (lifting) NNode_asNNode Tree_unf_NNode)

(* Coiteration *)
definition TTree_coit ::
"('b \<Rightarrow> N) \<Rightarrow> ('b \<Rightarrow> (T + 'b) fset) \<Rightarrow> 'b \<Rightarrow> Tree"
where "TTree_coit rt ct \<equiv> Tree_unf_coiter <rt,ct>"

lemma Tree_coit_coit:
"Tree_unf_coiter s = TTree_coit (fst o s) (snd o s)"
apply(rule ext)
unfolding TTree_coit_def by simp

theorem TTree_coit:
"root (TTree_coit rt ct b) = rt b"
"ccont (TTree_coit rt ct b) = map_fset (id \<oplus> TTree_coit rt ct) (ct b)"
using Tree.unf_coiters[of "<rt,ct>" b] unfolding Tree_coit_coit fst_convol snd_convol
unfolding pre_Tree_map' fst_convol' snd_convol'
unfolding Tree_unf_root_ccont by simp_all

(* Corecursion, stronger than coiteration *)
definition TTree_corec ::
"('b \<Rightarrow> N) \<Rightarrow> ('b \<Rightarrow> (T + (Tree + 'b)) fset) \<Rightarrow> 'b \<Rightarrow> Tree"
where "TTree_corec rt ct \<equiv> Tree_unf_corec <rt,ct>"

lemma Tree_unf_corec_corec:
"Tree_unf_corec s = TTree_corec (fst o s) (snd o s)"
apply(rule ext)
unfolding TTree_corec_def by simp

theorem TTree_corec:
"root (TTree_corec rt ct b) = rt b"
"ccont (TTree_corec rt ct b) = map_fset (id \<oplus> ([[id, TTree_corec rt ct]]) ) (ct b)"
using Tree.unf_corecs[of "<rt,ct>" b] unfolding Tree_unf_corec_corec fst_convol snd_convol
unfolding pre_Tree_map' fst_convol' snd_convol'
unfolding Tree_unf_root_ccont by simp_all


subsection{* The characteristic theorems transported from fset to set *}

definition "Node n as \<equiv> NNode n (the_inv fset as)"
definition "cont \<equiv> fset o ccont"
definition "coit rt ct \<equiv> TTree_coit rt (the_inv fset o ct)"
definition "corec rt ct \<equiv> TTree_corec rt (the_inv fset o ct)"

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
using NNode_root_ccont unfolding Node_def cont_def
by (metis cont_def finite_cont fset_cong fset_to_fset o_def)

theorem Tree_simps[simp]:
assumes "finite as" and "finite as'"
shows "Node n as = Node n' as' \<longleftrightarrow> n = n' \<and> as = as'"
using assms TTree_simps unfolding Node_def
by (metis fset_to_fset)

theorem Tree_cases[elim, case_names Node Choice]:
assumes Node: "\<And> n as. \<lbrakk>finite as; tr = Node n as\<rbrakk> \<Longrightarrow> phi"
shows phi
apply(cases rule: TTree_cases[of tr])
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
using phi apply(induct rule: TTree_coind_Node)
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

theorem coit:
"root (coit rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (coit rt ct b) = image (id \<oplus> coit rt ct) (ct b)"
using TTree_coit[of rt "the_inv fset \<circ> ct" b] unfolding coit_def
apply - apply metis
unfolding cont_def comp_def
by (metis (no_types) fset_to_fset map_fset_image)


theorem corec:
"root (corec rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (corec rt ct b) = image (id \<oplus> ([[id, corec rt ct]])) (ct b)"
using TTree_corec[of rt "the_inv fset \<circ> ct" b] unfolding corec_def
apply - apply metis
unfolding cont_def comp_def
by (metis (no_types) fset_to_fset map_fset_image)


end
