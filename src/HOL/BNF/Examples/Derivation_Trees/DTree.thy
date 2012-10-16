(*  Title:      HOL/BNF/Examples/Infinite_Derivation_Trees/DTree.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Derivation trees with nonterminal internal nodes and terminal leaves.
*)

header {* Trees with Nonterminal Internal Nodes and Terminal Leaves *}

theory DTree
imports Prelim
begin

hide_fact (open) Quotient_Product.prod_rel_def

typedecl N
typedecl T

codata dtree = NNode (root: N) (ccont: "(T + dtree) fset")


subsection{* The characteristic lemmas transported from fset to set *}

definition "Node n as \<equiv> NNode n (the_inv fset as)"
definition "cont \<equiv> fset o ccont"
definition "unfold rt ct \<equiv> dtree_unfold rt (the_inv fset o ct)"
definition "corec rt qt ct dt \<equiv> dtree_corec rt qt (the_inv fset o ct) (the_inv fset o dt)"

lemma finite_cont[simp]: "finite (cont tr)"
unfolding cont_def by auto

lemma Node_root_cont[simp]:
"Node (root tr) (cont tr) = tr"
using dtree.collapse unfolding Node_def cont_def
by (metis cont_def finite_cont fset_cong fset_to_fset o_def)

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

lemma dtree_sel_ctor[simp]:
"root (Node n as) = n"
"finite as \<Longrightarrow> cont (Node n as) = as"
unfolding Node_def cont_def by auto

lemmas root_Node = dtree_sel_ctor(1)
lemmas cont_Node = dtree_sel_ctor(2)

lemma dtree_cong:
assumes "root tr = root tr'" and "cont tr = cont tr'"
shows "tr = tr'"
by (metis Node_root_cont assms)

lemma set_rel_cont: 
"set_rel \<chi> (cont tr1) (cont tr2) = fset_rel \<chi> (ccont tr1) (ccont tr2)"
unfolding cont_def comp_def fset_rel_fset ..

lemma dtree_coinduct[elim, consumes 1, case_names Lift, induct pred: "HOL.eq"]:
assumes phi: "\<phi> tr1 tr2" and
Lift: "\<And> tr1 tr2. \<phi> tr1 tr2 \<Longrightarrow>
                  root tr1 = root tr2 \<and> set_rel (sum_rel op = \<phi>) (cont tr1) (cont tr2)"
shows "tr1 = tr2"
using phi apply(elim dtree.coinduct)
apply(rule Lift[unfolded set_rel_cont]) . 
 
lemma unfold:
"root (unfold rt ct b) = rt b"
"finite (ct b) \<Longrightarrow> cont (unfold rt ct b) = image (id \<oplus> unfold rt ct) (ct b)"
using dtree.sel_unfold[of rt "the_inv fset \<circ> ct" b] unfolding unfold_def
apply - apply metis
unfolding cont_def comp_def
by (metis (no_types) fset_to_fset map_fset_image)

lemma corec:
"root (corec rt qt ct dt b) = rt b"
"\<lbrakk>finite (ct b); finite (dt b)\<rbrakk> \<Longrightarrow>
 cont (corec rt qt ct dt b) =
 (if qt b then ct b else image (id \<oplus> corec rt qt ct dt) (dt b))"
using dtree.sel_corec[of rt qt "the_inv fset \<circ> ct" "the_inv fset \<circ> dt" b] 
unfolding corec_def
apply -
apply simp
unfolding cont_def comp_def id_def
by (metis (no_types) fset_to_fset map_fset_image)

end
