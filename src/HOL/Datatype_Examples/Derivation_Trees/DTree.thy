(*  Title:      HOL/Datatype_Examples/Derivation_Trees/DTree.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Derivation trees with nonterminal internal nodes and terminal leaves.
*)

header {* Trees with Nonterminal Internal Nodes and Terminal Leaves *}

theory DTree
imports Prelim
begin

typedecl N
typedecl T

codatatype dtree = NNode (root: N) (ccont: "(T + dtree) fset")

subsection{* Transporting the Characteristic Lemmas from @{text "fset"} to @{text "set"} *}

definition "Node n as \<equiv> NNode n (the_inv fset as)"
definition "cont \<equiv> fset o ccont"
definition "unfold rt ct \<equiv> corec_dtree rt (the_inv fset o image (map_sum id Inr) o ct)"
definition "corec rt ct \<equiv> corec_dtree rt (the_inv fset o ct)"

lemma finite_cont[simp]: "finite (cont tr)"
  unfolding cont_def comp_apply by (cases tr, clarsimp)

lemma Node_root_cont[simp]:
  "Node (root tr) (cont tr) = tr"
  unfolding Node_def cont_def comp_apply
  apply (rule trans[OF _ dtree.collapse])
  apply (rule arg_cong2[OF refl the_inv_into_f_f[unfolded inj_on_def]])
  apply (simp_all add: fset_inject)
  done

lemma dtree_simps[simp]:
assumes "finite as" and "finite as'"
shows "Node n as = Node n' as' \<longleftrightarrow> n = n' \<and> as = as'"
using assms dtree.inject unfolding Node_def
by (metis fset_to_fset)

lemma dtree_cases[elim, case_names Node Choice]:
assumes Node: "\<And> n as. \<lbrakk>finite as; tr = Node n as\<rbrakk> \<Longrightarrow> phi"
shows phi
apply(cases rule: dtree.exhaust[of tr])
using Node unfolding Node_def
by (metis Node Node_root_cont finite_cont)

lemma dtree_sel_ctr[simp]:
"root (Node n as) = n"
"finite as \<Longrightarrow> cont (Node n as) = as"
unfolding Node_def cont_def by auto

lemmas root_Node = dtree_sel_ctr(1)
lemmas cont_Node = dtree_sel_ctr(2)

lemma dtree_cong:
assumes "root tr = root tr'" and "cont tr = cont tr'"
shows "tr = tr'"
by (metis Node_root_cont assms)

lemma rel_set_cont:
"rel_set \<chi> (cont tr1) (cont tr2) = rel_fset \<chi> (ccont tr1) (ccont tr2)"
unfolding cont_def comp_def rel_fset_fset ..

lemma dtree_coinduct[elim, consumes 1, case_names Lift, induct pred: "HOL.eq"]:
assumes phi: "\<phi> tr1 tr2" and
Lift: "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow>
                  root tr1 = root tr2 \<and> rel_set (rel_sum op = \<phi>) (cont tr1) (cont tr2)"
shows "tr1 = tr2"
using phi apply(elim dtree.coinduct)
apply(rule Lift[unfolded rel_set_cont]) .

lemma unfold:
"root (unfold rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (unfold rt ct b) = image (id \<oplus> unfold rt ct) (ct b)"
using dtree.corec_sel[of rt "the_inv fset o image (map_sum id Inr) o ct" b] unfolding unfold_def
apply blast
unfolding cont_def comp_def
by (simp add: case_sum_o_inj map_sum.compositionality image_image)

lemma corec:
"root (corec rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (corec rt ct b) = image (id \<oplus> ([[id, corec rt ct]])) (ct b)"
using dtree.corec_sel[of rt "the_inv fset \<circ> ct" b] unfolding corec_def
unfolding cont_def comp_def id_def
by simp_all

end
