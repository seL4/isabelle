(*  Title:      HOL/Codatatype/Examples/Infinite_Derivation_Trees/Gram_Lang.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Language of a grammar.
*)

header {* Language of a Grammar *}

theory Gram_Lang
imports Tree
begin 


consts P :: "(N \<times> (T + N) set) set"
axiomatization where 
    finite_N: "finite (UNIV::N set)"
and finite_in_P: "\<And> n tns. (n,tns) \<in> P \<longrightarrow> finite tns"
and used: "\<And> n. \<exists> tns. (n,tns) \<in> P"


subsection{* Tree basics: frontier, interior, etc. *}

lemma Tree_cong: 
assumes "root tr = root tr'" and "cont tr = cont tr'"
shows "tr = tr'"
by (metis Node_root_cont assms)

inductive finiteT where 
Node: "\<lbrakk>finite as; (finiteT^#) as\<rbrakk> \<Longrightarrow> finiteT (Node a as)"
monos lift_mono

lemma finiteT_induct[consumes 1, case_names Node, induct pred: finiteT]:
assumes 1: "finiteT tr"
and IH: "\<And>as n. \<lbrakk>finite as; (\<phi>^#) as\<rbrakk> \<Longrightarrow> \<phi> (Node n as)"
shows "\<phi> tr"
using 1 apply(induct rule: finiteT.induct)
apply(rule IH) apply assumption apply(elim mono_lift) by simp


(* Frontier *)

inductive inFr :: "N set \<Rightarrow> Tree \<Rightarrow> T \<Rightarrow> bool" where 
Base: "\<lbrakk>root tr \<in> ns; Inl t \<in> cont tr\<rbrakk> \<Longrightarrow> inFr ns tr t"
|
Ind: "\<lbrakk>root tr \<in> ns; Inr tr1 \<in> cont tr; inFr ns tr1 t\<rbrakk> \<Longrightarrow> inFr ns tr t"

definition "Fr ns tr \<equiv> {t. inFr ns tr t}"

lemma inFr_root_in: "inFr ns tr t \<Longrightarrow> root tr \<in> ns"
by (metis inFr.simps)

lemma inFr_mono: 
assumes "inFr ns tr t" and "ns \<subseteq> ns'"
shows "inFr ns' tr t"
using assms apply(induct arbitrary: ns' rule: inFr.induct)
using Base Ind by (metis inFr.simps set_mp)+

lemma inFr_Ind_minus: 
assumes "inFr ns1 tr1 t" and "Inr tr1 \<in> cont tr"
shows "inFr (insert (root tr) ns1) tr t"
using assms apply(induct rule: inFr.induct)
  apply (metis inFr.simps insert_iff)
  by (metis inFr.simps inFr_mono insertI1 subset_insertI)

(* alternative definition *)
inductive inFr2 :: "N set \<Rightarrow> Tree \<Rightarrow> T \<Rightarrow> bool" where 
Base: "\<lbrakk>root tr \<in> ns; Inl t \<in> cont tr\<rbrakk> \<Longrightarrow> inFr2 ns tr t"
|
Ind: "\<lbrakk>Inr tr1 \<in> cont tr; inFr2 ns1 tr1 t\<rbrakk> 
      \<Longrightarrow> inFr2 (insert (root tr) ns1) tr t"

lemma inFr2_root_in: "inFr2 ns tr t \<Longrightarrow> root tr \<in> ns"
apply(induct rule: inFr2.induct) by auto

lemma inFr2_mono: 
assumes "inFr2 ns tr t" and "ns \<subseteq> ns'"
shows "inFr2 ns' tr t"
using assms apply(induct arbitrary: ns' rule: inFr2.induct)
using Base Ind
apply (metis subsetD) by (metis inFr2.simps insert_absorb insert_subset) 

lemma inFr2_Ind:
assumes "inFr2 ns tr1 t" and "root tr \<in> ns" and "Inr tr1 \<in> cont tr" 
shows "inFr2 ns tr t"
using assms apply(induct rule: inFr2.induct)
  apply (metis inFr2.simps insert_absorb)
  by (metis inFr2.simps insert_absorb)  

lemma inFr_inFr2:
"inFr = inFr2"
apply (rule ext)+  apply(safe)
  apply(erule inFr.induct)
    apply (metis (lifting) inFr2.Base)
    apply (metis (lifting) inFr2_Ind) 
  apply(erule inFr2.induct)
    apply (metis (lifting) inFr.Base)
    apply (metis (lifting) inFr_Ind_minus)
done  

lemma not_root_inFr:
assumes "root tr \<notin> ns"
shows "\<not> inFr ns tr t"
by (metis assms inFr_root_in)

theorem not_root_Fr:
assumes "root tr \<notin> ns"
shows "Fr ns tr = {}"
using not_root_inFr[OF assms] unfolding Fr_def by auto 


(* Interior *)

inductive inItr :: "N set \<Rightarrow> Tree \<Rightarrow> N \<Rightarrow> bool" where 
Base: "root tr \<in> ns \<Longrightarrow> inItr ns tr (root tr)"
|
Ind: "\<lbrakk>root tr \<in> ns; Inr tr1 \<in> cont tr; inItr ns tr1 n\<rbrakk> \<Longrightarrow> inItr ns tr n"

definition "Itr ns tr \<equiv> {n. inItr ns tr n}"

lemma inItr_root_in: "inItr ns tr n \<Longrightarrow> root tr \<in> ns"
by (metis inItr.simps) 

lemma inItr_mono: 
assumes "inItr ns tr n" and "ns \<subseteq> ns'"
shows "inItr ns' tr n"
using assms apply(induct arbitrary: ns' rule: inItr.induct)
using Base Ind by (metis inItr.simps set_mp)+


(* The subtree relation *)  

inductive subtr where 
Refl: "root tr \<in> ns \<Longrightarrow> subtr ns tr tr"
|
Step: "\<lbrakk>root tr3 \<in> ns; subtr ns tr1 tr2; Inr tr2 \<in> cont tr3\<rbrakk> \<Longrightarrow> subtr ns tr1 tr3"

lemma subtr_rootL_in: 
assumes "subtr ns tr1 tr2"
shows "root tr1 \<in> ns"
using assms apply(induct rule: subtr.induct) by auto

lemma subtr_rootR_in: 
assumes "subtr ns tr1 tr2"
shows "root tr2 \<in> ns"
using assms apply(induct rule: subtr.induct) by auto

lemmas subtr_roots_in = subtr_rootL_in subtr_rootR_in

lemma subtr_mono: 
assumes "subtr ns tr1 tr2" and "ns \<subseteq> ns'"
shows "subtr ns' tr1 tr2"
using assms apply(induct arbitrary: ns' rule: subtr.induct)
using Refl Step by (metis subtr.simps set_mp)+

lemma subtr_trans_Un:
assumes "subtr ns12 tr1 tr2" and "subtr ns23 tr2 tr3"
shows "subtr (ns12 \<union> ns23) tr1 tr3"
proof-
  have "subtr ns23 tr2 tr3  \<Longrightarrow> 
        (\<forall> ns12 tr1. subtr ns12 tr1 tr2 \<longrightarrow> subtr (ns12 \<union> ns23) tr1 tr3)"
  apply(induct  rule: subtr.induct, safe)
    apply (metis subtr_mono sup_commute sup_ge2)
    by (metis (lifting) Step UnI2) 
  thus ?thesis using assms by auto
qed

lemma subtr_trans:
assumes "subtr ns tr1 tr2" and "subtr ns tr2 tr3"
shows "subtr ns tr1 tr3"
using subtr_trans_Un[OF assms] by simp

lemma subtr_StepL: 
assumes r: "root tr1 \<in> ns" and tr12: "Inr tr1 \<in> cont tr2" and s: "subtr ns tr2 tr3"
shows "subtr ns tr1 tr3"
apply(rule subtr_trans[OF _ s]) apply(rule Step[of tr2 ns tr1 tr1])
by (metis assms subtr_rootL_in Refl)+

(* alternative definition: *)
inductive subtr2 where 
Refl: "root tr \<in> ns \<Longrightarrow> subtr2 ns tr tr"
|
Step: "\<lbrakk>root tr1 \<in> ns; Inr tr1 \<in> cont tr2; subtr2 ns tr2 tr3\<rbrakk> \<Longrightarrow> subtr2 ns tr1 tr3"

lemma subtr2_rootL_in: 
assumes "subtr2 ns tr1 tr2"
shows "root tr1 \<in> ns"
using assms apply(induct rule: subtr2.induct) by auto

lemma subtr2_rootR_in: 
assumes "subtr2 ns tr1 tr2"
shows "root tr2 \<in> ns"
using assms apply(induct rule: subtr2.induct) by auto

lemmas subtr2_roots_in = subtr2_rootL_in subtr2_rootR_in

lemma subtr2_mono: 
assumes "subtr2 ns tr1 tr2" and "ns \<subseteq> ns'"
shows "subtr2 ns' tr1 tr2"
using assms apply(induct arbitrary: ns' rule: subtr2.induct)
using Refl Step by (metis subtr2.simps set_mp)+

lemma subtr2_trans_Un:
assumes "subtr2 ns12 tr1 tr2" and "subtr2 ns23 tr2 tr3"
shows "subtr2 (ns12 \<union> ns23) tr1 tr3"
proof-
  have "subtr2 ns12 tr1 tr2  \<Longrightarrow> 
        (\<forall> ns23 tr3. subtr2 ns23 tr2 tr3 \<longrightarrow> subtr2 (ns12 \<union> ns23) tr1 tr3)"
  apply(induct  rule: subtr2.induct, safe)
    apply (metis subtr2_mono sup_commute sup_ge2)
    by (metis Un_iff subtr2.simps)
  thus ?thesis using assms by auto
qed

lemma subtr2_trans:
assumes "subtr2 ns tr1 tr2" and "subtr2 ns tr2 tr3"
shows "subtr2 ns tr1 tr3"
using subtr2_trans_Un[OF assms] by simp

lemma subtr2_StepR: 
assumes r: "root tr3 \<in> ns" and tr23: "Inr tr2 \<in> cont tr3" and s: "subtr2 ns tr1 tr2"
shows "subtr2 ns tr1 tr3"
apply(rule subtr2_trans[OF s]) apply(rule Step[of _ _ tr3])
by (metis assms subtr2_rootR_in Refl)+

lemma subtr_subtr2:
"subtr = subtr2"
apply (rule ext)+  apply(safe)
  apply(erule subtr.induct)
    apply (metis (lifting) subtr2.Refl)
    apply (metis (lifting) subtr2_StepR) 
  apply(erule subtr2.induct)
    apply (metis (lifting) subtr.Refl)
    apply (metis (lifting) subtr_StepL)
done

lemma subtr_inductL[consumes 1, case_names Refl Step]:
assumes s: "subtr ns tr1 tr2" and Refl: "\<And>ns tr. \<phi> ns tr tr"
and Step: 
"\<And>ns tr1 tr2 tr3. 
   \<lbrakk>root tr1 \<in> ns; Inr tr1 \<in> cont tr2; subtr ns tr2 tr3; \<phi> ns tr2 tr3\<rbrakk> \<Longrightarrow> \<phi> ns tr1 tr3"
shows "\<phi> ns tr1 tr2"
using s unfolding subtr_subtr2 apply(rule subtr2.induct)
using Refl Step unfolding subtr_subtr2 by auto

lemma subtr_UNIV_inductL[consumes 1, case_names Refl Step]:
assumes s: "subtr UNIV tr1 tr2" and Refl: "\<And>tr. \<phi> tr tr"
and Step: 
"\<And>tr1 tr2 tr3. 
   \<lbrakk>Inr tr1 \<in> cont tr2; subtr UNIV tr2 tr3; \<phi> tr2 tr3\<rbrakk> \<Longrightarrow> \<phi> tr1 tr3"
shows "\<phi> tr1 tr2"
using s apply(induct rule: subtr_inductL)
apply(rule Refl) using Step subtr_mono by (metis subset_UNIV)

(* Subtree versus frontier: *)
lemma subtr_inFr:
assumes "inFr ns tr t" and "subtr ns tr tr1" 
shows "inFr ns tr1 t"
proof-
  have "subtr ns tr tr1 \<Longrightarrow> (\<forall> t. inFr ns tr t \<longrightarrow> inFr ns tr1 t)"
  apply(induct rule: subtr.induct, safe) by (metis inFr.Ind)
  thus ?thesis using assms by auto
qed

corollary Fr_subtr: 
"Fr ns tr = \<Union> {Fr ns tr' | tr'. subtr ns tr' tr}"
unfolding Fr_def proof safe
  fix t assume t: "inFr ns tr t"  hence "root tr \<in> ns" by (rule inFr_root_in)  
  thus "t \<in> \<Union>{{t. inFr ns tr' t} |tr'. subtr ns tr' tr}"
  apply(intro UnionI[of "{t. inFr ns tr t}" _ t]) using t subtr.Refl by auto
qed(metis subtr_inFr)

lemma inFr_subtr:
assumes "inFr ns tr t" 
shows "\<exists> tr'. subtr ns tr' tr \<and> Inl t \<in> cont tr'"
using assms apply(induct rule: inFr.induct) apply safe
  apply (metis subtr.Refl)
  by (metis (lifting) subtr.Step)

corollary Fr_subtr_cont: 
"Fr ns tr = \<Union> {Inl -` cont tr' | tr'. subtr ns tr' tr}"
unfolding Fr_def
apply safe
apply (frule inFr_subtr)
apply auto
by (metis inFr.Base subtr_inFr subtr_rootL_in)

(* Subtree versus interior: *)
lemma subtr_inItr:
assumes "inItr ns tr n" and "subtr ns tr tr1" 
shows "inItr ns tr1 n"
proof-
  have "subtr ns tr tr1 \<Longrightarrow> (\<forall> t. inItr ns tr n \<longrightarrow> inItr ns tr1 n)"
  apply(induct rule: subtr.induct, safe) by (metis inItr.Ind)
  thus ?thesis using assms by auto
qed

corollary Itr_subtr: 
"Itr ns tr = \<Union> {Itr ns tr' | tr'. subtr ns tr' tr}"
unfolding Itr_def apply safe
apply (metis (lifting, mono_tags) UnionI inItr_root_in mem_Collect_eq subtr.Refl)
by (metis subtr_inItr)

lemma inItr_subtr:
assumes "inItr ns tr n" 
shows "\<exists> tr'. subtr ns tr' tr \<and> root tr' = n"
using assms apply(induct rule: inItr.induct) apply safe
  apply (metis subtr.Refl)
  by (metis (lifting) subtr.Step)

corollary Itr_subtr_cont: 
"Itr ns tr = {root tr' | tr'. subtr ns tr' tr}"
unfolding Itr_def apply safe
  apply (metis (lifting, mono_tags) UnionI inItr_subtr mem_Collect_eq vimageI2)
  by (metis inItr.Base subtr_inItr subtr_rootL_in)


subsection{* The immediate subtree function *}

(* production of: *)
abbreviation "prodOf tr \<equiv> (id \<oplus> root) ` (cont tr)"
(* subtree of: *)
definition "subtrOf tr n \<equiv> SOME tr'. Inr tr' \<in> cont tr \<and> root tr' = n"

lemma subtrOf: 
assumes n: "Inr n \<in> prodOf tr"
shows "Inr (subtrOf tr n) \<in> cont tr \<and> root (subtrOf tr n) = n"
proof-
  obtain tr' where "Inr tr' \<in> cont tr \<and> root tr' = n"
  using n unfolding image_def by (metis (lifting) Inr_oplus_elim assms)
  thus ?thesis unfolding subtrOf_def by(rule someI)
qed

lemmas Inr_subtrOf = subtrOf[THEN conjunct1]
lemmas root_subtrOf[simp] = subtrOf[THEN conjunct2]

lemma Inl_prodOf: "Inl -` (prodOf tr) = Inl -` (cont tr)"
proof safe
  fix t ttr assume "Inl t = (id \<oplus> root) ttr" and "ttr \<in> cont tr"
  thus "t \<in> Inl -` cont tr" by(cases ttr, auto)
next
  fix t assume "Inl t \<in> cont tr" thus "t \<in> Inl -` prodOf tr"
  by (metis (lifting) id_def image_iff sum_map.simps(1) vimageI2)
qed

lemma root_prodOf:
assumes "Inr tr' \<in> cont tr"
shows "Inr (root tr') \<in> prodOf tr"
by (metis (lifting) assms image_iff sum_map.simps(2))


subsection{* Derivation trees *}  

coinductive dtree where 
Tree: "\<lbrakk>(root tr, (id \<oplus> root) ` (cont tr)) \<in> P; inj_on root (Inr -` cont tr);
        lift dtree (cont tr)\<rbrakk> \<Longrightarrow> dtree tr"
monos lift_mono

(* destruction rules: *)
lemma dtree_P: 
assumes "dtree tr"
shows "(root tr, (id \<oplus> root) ` (cont tr)) \<in> P"
using assms unfolding dtree.simps by auto

lemma dtree_inj_on: 
assumes "dtree tr"
shows "inj_on root (Inr -` cont tr)"
using assms unfolding dtree.simps by auto

lemma dtree_inj[simp]: 
assumes "dtree tr" and "Inr tr1 \<in> cont tr" and "Inr tr2 \<in> cont tr"
shows "root tr1 = root tr2 \<longleftrightarrow> tr1 = tr2"
using assms dtree_inj_on unfolding inj_on_def by auto

lemma dtree_lift: 
assumes "dtree tr"
shows "lift dtree (cont tr)"
using assms unfolding dtree.simps by auto


(* coinduction:*)
lemma dtree_coind[elim, consumes 1, case_names Hyp]: 
assumes phi: "\<phi> tr"
and Hyp: 
"\<And> tr. \<phi> tr \<Longrightarrow> 
       (root tr, image (id \<oplus> root) (cont tr)) \<in> P \<and> 
       inj_on root (Inr -` cont tr) \<and> 
       lift (\<lambda> tr. \<phi> tr \<or> dtree tr) (cont tr)"
shows "dtree tr"
apply(rule dtree.coinduct[of \<phi> tr, OF phi]) 
using Hyp by blast

lemma dtree_raw_coind[elim, consumes 1, case_names Hyp]: 
assumes phi: "\<phi> tr"
and Hyp: 
"\<And> tr. \<phi> tr \<Longrightarrow> 
       (root tr, image (id \<oplus> root) (cont tr)) \<in> P \<and>
       inj_on root (Inr -` cont tr) \<and> 
       lift \<phi> (cont tr)"
shows "dtree tr"
using phi apply(induct rule: dtree_coind)
using Hyp mono_lift 
by (metis (mono_tags) mono_lift)

lemma dtree_subtr_inj_on: 
assumes d: "dtree tr1" and s: "subtr ns tr tr1"
shows "inj_on root (Inr -` cont tr)"
using s d apply(induct rule: subtr.induct)
apply (metis (lifting) dtree_inj_on) by (metis dtree_lift lift_def)

lemma dtree_subtr_P: 
assumes d: "dtree tr1" and s: "subtr ns tr tr1"
shows "(root tr, (id \<oplus> root) ` cont tr) \<in> P"
using s d apply(induct rule: subtr.induct)
apply (metis (lifting) dtree_P) by (metis dtree_lift lift_def)

lemma subtrOf_root[simp]:
assumes tr: "dtree tr" and cont: "Inr tr' \<in> cont tr"
shows "subtrOf tr (root tr') = tr'"
proof-
  have 0: "Inr (subtrOf tr (root tr')) \<in> cont tr" using Inr_subtrOf
  by (metis (lifting) cont root_prodOf)
  have "root (subtrOf tr (root tr')) = root tr'"
  using root_subtrOf by (metis (lifting) cont root_prodOf)
  thus ?thesis unfolding dtree_inj[OF tr 0 cont] .
qed

lemma surj_subtrOf: 
assumes "dtree tr" and 0: "Inr tr' \<in> cont tr"
shows "\<exists> n. Inr n \<in> prodOf tr \<and> subtrOf tr n = tr'"
apply(rule exI[of _ "root tr'"]) 
using root_prodOf[OF 0] subtrOf_root[OF assms] by simp

lemma dtree_subtr: 
assumes "dtree tr1" and "subtr ns tr tr1"
shows "dtree tr" 
proof-
  have "(\<exists> ns tr1. dtree tr1 \<and> subtr ns tr tr1) \<Longrightarrow> dtree tr"
  proof (induct rule: dtree_raw_coind)
    case (Hyp tr)
    then obtain ns tr1 where tr1: "dtree tr1" and tr_tr1: "subtr ns tr tr1" by auto
    show ?case unfolding lift_def proof safe
      show "(root tr, (id \<oplus> root) ` cont tr) \<in> P" using dtree_subtr_P[OF tr1 tr_tr1] .
    next 
      show "inj_on root (Inr -` cont tr)" using dtree_subtr_inj_on[OF tr1 tr_tr1] .
    next
      fix tr' assume tr': "Inr tr' \<in> cont tr"
      have tr_tr1: "subtr (ns \<union> {root tr'}) tr tr1" using subtr_mono[OF tr_tr1] by auto
      have "subtr (ns \<union> {root tr'}) tr' tr1" using subtr_StepL[OF _ tr' tr_tr1] by auto
      thus "\<exists>ns' tr1. dtree tr1 \<and> subtr ns' tr' tr1" using tr1 by blast
    qed
  qed
  thus ?thesis using assms by auto
qed


subsection{* Default trees *}

(* Pick a left-hand side of a production for each nonterminal *)
definition S where "S n \<equiv> SOME tns. (n,tns) \<in> P"

lemma S_P: "(n, S n) \<in> P"
using used unfolding S_def by(rule someI_ex)

lemma finite_S: "finite (S n)"
using S_P finite_in_P by auto 


(* The default tree of a nonterminal *)
definition deftr :: "N \<Rightarrow> Tree" where  
"deftr \<equiv> coit id S"

lemma deftr_simps[simp]:
"root (deftr n) = n" 
"cont (deftr n) = image (id \<oplus> deftr) (S n)"
using coit(1)[of id S n] coit(2)[of S n id, OF finite_S] 
unfolding deftr_def by simp_all

lemmas root_deftr = deftr_simps(1)
lemmas cont_deftr = deftr_simps(2)

lemma root_o_deftr[simp]: "root o deftr = id"
by (rule ext, auto)

lemma dtree_deftr: "dtree (deftr n)"
proof-
  {fix tr assume "\<exists> n. tr = deftr n" hence "dtree tr"
   apply(induct rule: dtree_raw_coind) apply safe
   unfolding deftr_simps image_compose[symmetric] sum_map.comp id_o
   root_o_deftr sum_map.id image_id id_apply apply(rule S_P) 
   unfolding inj_on_def lift_def by auto   
  }
  thus ?thesis by auto
qed


subsection{* Hereditary substitution *}

(* Auxiliary concept: The root-ommiting frontier: *)
definition "inFrr ns tr t \<equiv> \<exists> tr'. Inr tr' \<in> cont tr \<and> inFr ns tr' t"
definition "Frr ns tr \<equiv> {t. \<exists> tr'. Inr tr' \<in> cont tr \<and> t \<in> Fr ns tr'}"

context 
fixes tr0 :: Tree 
begin

definition "hsubst_r tr \<equiv> root tr"
definition "hsubst_c tr \<equiv> if root tr = root tr0 then cont tr0 else cont tr"

(* Hereditary substitution: *)
definition hsubst :: "Tree \<Rightarrow> Tree" where  
"hsubst \<equiv> coit hsubst_r hsubst_c"

lemma finite_hsubst_c: "finite (hsubst_c n)"
unfolding hsubst_c_def by (metis finite_cont) 

lemma root_hsubst[simp]: "root (hsubst tr) = root tr"
using coit(1)[of hsubst_r hsubst_c tr] unfolding hsubst_def hsubst_r_def by simp

lemma root_o_subst[simp]: "root o hsubst = root"
unfolding comp_def root_hsubst ..

lemma cont_hsubst_eq[simp]:
assumes "root tr = root tr0"
shows "cont (hsubst tr) = (id \<oplus> hsubst) ` (cont tr0)"
apply(subst id_o[symmetric, of id]) unfolding id_o
using coit(2)[of hsubst_c tr hsubst_r, OF finite_hsubst_c] 
unfolding hsubst_def hsubst_c_def using assms by simp

lemma hsubst_eq:
assumes "root tr = root tr0"
shows "hsubst tr = hsubst tr0" 
apply(rule Tree_cong) using assms cont_hsubst_eq by auto

lemma cont_hsubst_neq[simp]:
assumes "root tr \<noteq> root tr0"
shows "cont (hsubst tr) = (id \<oplus> hsubst) ` (cont tr)"
apply(subst id_o[symmetric, of id]) unfolding id_o
using coit(2)[of hsubst_c tr hsubst_r, OF finite_hsubst_c] 
unfolding hsubst_def hsubst_c_def using assms by simp

lemma Inl_cont_hsubst_eq[simp]:
assumes "root tr = root tr0"
shows "Inl -` cont (hsubst tr) = Inl -` (cont tr0)"
unfolding cont_hsubst_eq[OF assms] by simp

lemma Inr_cont_hsubst_eq[simp]:
assumes "root tr = root tr0"
shows "Inr -` cont (hsubst tr) = hsubst ` Inr -` cont tr0"
unfolding cont_hsubst_eq[OF assms] by simp

lemma Inl_cont_hsubst_neq[simp]:
assumes "root tr \<noteq> root tr0"
shows "Inl -` cont (hsubst tr) = Inl -` (cont tr)"
unfolding cont_hsubst_neq[OF assms] by simp

lemma Inr_cont_hsubst_neq[simp]:
assumes "root tr \<noteq> root tr0"
shows "Inr -` cont (hsubst tr) = hsubst ` Inr -` cont tr"
unfolding cont_hsubst_neq[OF assms] by simp  

lemma dtree_hsubst:
assumes tr0: "dtree tr0" and tr: "dtree tr"
shows "dtree (hsubst tr)"
proof-
  {fix tr1 have "(\<exists> tr. dtree tr \<and> tr1 = hsubst tr) \<Longrightarrow> dtree tr1" 
   proof (induct rule: dtree_raw_coind)
     case (Hyp tr1) then obtain tr 
     where dtr: "dtree tr" and tr1: "tr1 = hsubst tr" by auto
     show ?case unfolding lift_def tr1 proof safe
       show "(root (hsubst tr), prodOf (hsubst tr)) \<in> P"
       unfolding tr1 apply(cases "root tr = root tr0") 
       using  dtree_P[OF dtr] dtree_P[OF tr0] 
       by (auto simp add: image_compose[symmetric] sum_map.comp)
       show "inj_on root (Inr -` cont (hsubst tr))" 
       apply(cases "root tr = root tr0") using dtree_inj_on[OF dtr] dtree_inj_on[OF tr0] 
       unfolding inj_on_def by (auto, blast)
       fix tr' assume "Inr tr' \<in> cont (hsubst tr)"
       thus "\<exists>tra. dtree tra \<and> tr' = hsubst tra"
       apply(cases "root tr = root tr0", simp_all)
         apply (metis dtree_lift lift_def tr0)
         by (metis dtr dtree_lift lift_def)
     qed
   qed
  }
  thus ?thesis using assms by blast
qed 

lemma Frr: "Frr ns tr = {t. inFrr ns tr t}"
unfolding inFrr_def Frr_def Fr_def by auto

lemma inFr_hsubst_imp: 
assumes "inFr ns (hsubst tr) t"
shows "t \<in> Inl -` (cont tr0) \<or> inFrr (ns - {root tr0}) tr0 t \<or> 
       inFr (ns - {root tr0}) tr t"
proof-
  {fix tr1 
   have "inFr ns tr1 t \<Longrightarrow> 
   (\<And> tr. tr1 = hsubst tr \<Longrightarrow> (t \<in> Inl -` (cont tr0) \<or> inFrr (ns - {root tr0}) tr0 t \<or> 
                              inFr (ns - {root tr0}) tr t))"
   proof(induct rule: inFr.induct)
     case (Base tr1 ns t tr)
     hence rtr: "root tr1 \<in> ns" and t_tr1: "Inl t \<in> cont tr1" and tr1: "tr1 = hsubst tr"
     by auto
     show ?case
     proof(cases "root tr1 = root tr0")
       case True
       hence "t \<in> Inl -` (cont tr0)" using t_tr1 unfolding tr1 by auto
       thus ?thesis by simp
     next
       case False
       hence "inFr (ns - {root tr0}) tr t" using t_tr1 unfolding tr1 apply simp
       by (metis Base.prems Diff_iff root_hsubst inFr.Base rtr singletonE)
       thus ?thesis by simp
     qed
   next
     case (Ind tr1 ns tr1' t) note IH = Ind(4)
     have rtr1: "root tr1 \<in> ns" and tr1'_tr1: "Inr tr1' \<in> cont tr1"
     and t_tr1': "inFr ns tr1' t" and tr1: "tr1 = hsubst tr" using Ind by auto
     have rtr1: "root tr1 = root tr" unfolding tr1 by simp
     show ?case
     proof(cases "root tr1 = root tr0")
       case True
       then obtain tr' where tr'_tr0: "Inr tr' \<in> cont tr0" and tr1': "tr1' = hsubst tr'"
       using tr1'_tr1 unfolding tr1 by auto
       show ?thesis using IH[OF tr1'] proof (elim disjE)
         assume "inFr (ns - {root tr0}) tr' t"         
         thus ?thesis using tr'_tr0 unfolding inFrr_def by auto
       qed auto
     next
       case False 
       then obtain tr' where tr'_tr: "Inr tr' \<in> cont tr" and tr1': "tr1' = hsubst tr'"
       using tr1'_tr1 unfolding tr1 by auto
       show ?thesis using IH[OF tr1'] proof (elim disjE)
         assume "inFr (ns - {root tr0}) tr' t"         
         thus ?thesis using tr'_tr unfolding inFrr_def
         by (metis Diff_iff False Ind(1) empty_iff inFr2_Ind inFr_inFr2 insert_iff rtr1) 
       qed auto
     qed
   qed
  }
  thus ?thesis using assms by auto
qed 

lemma inFr_hsubst_notin:
assumes "inFr ns tr t" and "root tr0 \<notin> ns" 
shows "inFr ns (hsubst tr) t"
using assms apply(induct rule: inFr.induct)
apply (metis Inl_cont_hsubst_neq inFr2.Base inFr_inFr2 root_hsubst vimageD vimageI2)
by (metis (lifting) Inr_cont_hsubst_neq inFr.Ind rev_image_eqI root_hsubst vimageD vimageI2)

lemma inFr_hsubst_minus:
assumes "inFr (ns - {root tr0}) tr t"
shows "inFr ns (hsubst tr) t"
proof-
  have 1: "inFr (ns - {root tr0}) (hsubst tr) t"
  using inFr_hsubst_notin[OF assms] by simp
  show ?thesis using inFr_mono[OF 1] by auto
qed

lemma inFr_self_hsubst: 
assumes "root tr0 \<in> ns"
shows 
"inFr ns (hsubst tr0) t \<longleftrightarrow> 
 t \<in> Inl -` (cont tr0) \<or> inFrr (ns - {root tr0}) tr0 t"
(is "?A \<longleftrightarrow> ?B \<or> ?C")
apply(intro iffI)
apply (metis inFr_hsubst_imp Diff_iff inFr_root_in insertI1) proof(elim disjE)
  assume ?B thus ?A apply(intro inFr.Base) using assms by auto
next
  assume ?C then obtain tr where 
  tr_tr0: "Inr tr \<in> cont tr0" and t_tr: "inFr (ns - {root tr0}) tr t"  
  unfolding inFrr_def by auto
  def tr1 \<equiv> "hsubst tr"
  have 1: "inFr ns tr1 t" using t_tr unfolding tr1_def using inFr_hsubst_minus by auto
  have "Inr tr1 \<in> cont (hsubst tr0)" unfolding tr1_def using tr_tr0 by auto
  thus ?A using 1 inFr.Ind assms by (metis root_hsubst)
qed

theorem Fr_self_hsubst: 
assumes "root tr0 \<in> ns"
shows "Fr ns (hsubst tr0) = Inl -` (cont tr0) \<union> Frr (ns - {root tr0}) tr0"
using inFr_self_hsubst[OF assms] unfolding Frr Fr_def by auto

end (* context *)
  

subsection{* Regular trees *}

hide_const regular

definition "reg f tr \<equiv> \<forall> tr'. subtr UNIV tr' tr \<longrightarrow> tr' = f (root tr')"
definition "regular tr \<equiv> \<exists> f. reg f tr"

lemma reg_def2: "reg f tr \<longleftrightarrow> (\<forall> ns tr'. subtr ns tr' tr \<longrightarrow> tr' = f (root tr'))"
unfolding reg_def using subtr_mono by (metis subset_UNIV) 

lemma regular_def2: "regular tr \<longleftrightarrow> (\<exists> f. reg f tr \<and> (\<forall> n. root (f n) = n))"
unfolding regular_def proof safe
  fix f assume f: "reg f tr"
  def g \<equiv> "\<lambda> n. if inItr UNIV tr n then f n else deftr n"
  show "\<exists>g. reg g tr \<and> (\<forall>n. root (g n) = n)"
  apply(rule exI[of _ g])
  using f deftr_simps(1) unfolding g_def reg_def apply safe
    apply (metis (lifting) inItr.Base subtr_inItr subtr_rootL_in)
    by (metis (full_types) inItr_subtr subtr_subtr2)
qed auto

lemma reg_root: 
assumes "reg f tr"
shows "f (root tr) = tr"
using assms unfolding reg_def
by (metis (lifting) iso_tuple_UNIV_I subtr.Refl)


lemma reg_Inr_cont: 
assumes "reg f tr" and "Inr tr' \<in> cont tr"
shows "reg f tr'"
by (metis (lifting) assms iso_tuple_UNIV_I reg_def subtr.Step)

lemma reg_subtr: 
assumes "reg f tr" and "subtr ns tr' tr"
shows "reg f tr'"
using assms unfolding reg_def using subtr_trans[of UNIV tr] UNIV_I
by (metis UNIV_eq_I UnCI Un_upper1 iso_tuple_UNIV_I subtr_mono subtr_trans)

lemma regular_subtr: 
assumes r: "regular tr" and s: "subtr ns tr' tr"
shows "regular tr'"
using r reg_subtr[OF _ s] unfolding regular_def by auto

lemma subtr_deftr: 
assumes "subtr ns tr' (deftr n)"
shows "tr' = deftr (root tr')"
proof-
  {fix tr have "subtr ns tr' tr \<Longrightarrow> (\<forall> n. tr = deftr n \<longrightarrow> tr' = deftr (root tr'))"
   apply (induct rule: subtr.induct)
   proof(metis (lifting) deftr_simps(1), safe) 
     fix tr3 ns tr1 tr2 n
     assume 1: "root (deftr n) \<in> ns" and 2: "subtr ns tr1 tr2"
     and IH: "\<forall>n. tr2 = deftr n \<longrightarrow> tr1 = deftr (root tr1)" 
     and 3: "Inr tr2 \<in> cont (deftr n)"
     have "tr2 \<in> deftr ` UNIV" 
     using 3 unfolding deftr_simps image_def
     by (metis (lifting, full_types) 3 CollectI Inr_oplus_iff cont_deftr 
         iso_tuple_UNIV_I)
     then obtain n where "tr2 = deftr n" by auto
     thus "tr1 = deftr (root tr1)" using IH by auto
   qed 
  }
  thus ?thesis using assms by auto
qed

lemma reg_deftr: "reg deftr (deftr n)"
unfolding reg_def using subtr_deftr by auto

lemma dtree_subtrOf_Union: 
assumes "dtree tr" 
shows "\<Union>{K tr' |tr'. Inr tr' \<in> cont tr} =
       \<Union>{K (subtrOf tr n) |n. Inr n \<in> prodOf tr}"
unfolding Union_eq Bex_def mem_Collect_eq proof safe
  fix x xa tr'
  assume x: "x \<in> K tr'" and tr'_tr: "Inr tr' \<in> cont tr"
  show "\<exists>X. (\<exists>n. X = K (subtrOf tr n) \<and> Inr n \<in> prodOf tr) \<and> x \<in> X"
  apply(rule exI[of _ "K (subtrOf tr (root tr'))"]) apply(intro conjI)
    apply(rule exI[of _ "root tr'"]) apply (metis (lifting) root_prodOf tr'_tr)
    by (metis (lifting) assms subtrOf_root tr'_tr x)
next
  fix x X n ttr
  assume x: "x \<in> K (subtrOf tr n)" and n: "Inr n = (id \<oplus> root) ttr" and ttr: "ttr \<in> cont tr"
  show "\<exists>X. (\<exists>tr'. X = K tr' \<and> Inr tr' \<in> cont tr) \<and> x \<in> X"
  apply(rule exI[of _ "K (subtrOf tr n)"]) apply(intro conjI)
    apply(rule exI[of _ "subtrOf tr n"]) apply (metis imageI n subtrOf ttr)
    using x .
qed




subsection {* Paths in a regular tree *}

inductive path :: "(N \<Rightarrow> Tree) \<Rightarrow> N list \<Rightarrow> bool" for f where 
Base: "path f [n]"
|
Ind: "\<lbrakk>path f (n1 # nl); Inr (f n1) \<in> cont (f n)\<rbrakk> 
      \<Longrightarrow> path f (n # n1 # nl)"

lemma path_NE: 
assumes "path f nl"  
shows "nl \<noteq> Nil" 
using assms apply(induct rule: path.induct) by auto

lemma path_post: 
assumes f: "path f (n # nl)" and nl: "nl \<noteq> []"
shows "path f nl"
proof-
  obtain n1 nl1 where nl: "nl = n1 # nl1" using nl by (cases nl, auto)
  show ?thesis using assms unfolding nl using path.simps by (metis (lifting) list.inject) 
qed

lemma path_post_concat: 
assumes "path f (nl1 @ nl2)" and "nl2 \<noteq> Nil"
shows "path f nl2"
using assms apply (induct nl1)
apply (metis append_Nil) by (metis Nil_is_append_conv append_Cons path_post)

lemma path_concat: 
assumes "path f nl1" and "path f ((last nl1) # nl2)"
shows "path f (nl1 @ nl2)"
using assms apply(induct rule: path.induct) apply simp
by (metis append_Cons last.simps list.simps(3) path.Ind) 

lemma path_distinct:
assumes "path f nl"
shows "\<exists> nl'. path f nl' \<and> hd nl' = hd nl \<and> last nl' = last nl \<and> 
              set nl' \<subseteq> set nl \<and> distinct nl'"
using assms proof(induct rule: length_induct)
  case (1 nl)  hence p_nl: "path f nl" by simp
  then obtain n nl1 where nl: "nl = n # nl1" by (metis list.exhaust path_NE) 
  show ?case
  proof(cases nl1)
    case Nil
    show ?thesis apply(rule exI[of _ nl]) using path.Base unfolding nl Nil by simp
  next
    case (Cons n1 nl2)  
    hence p1: "path f nl1" by (metis list.simps nl p_nl path_post)
    show ?thesis
    proof(cases "n \<in> set nl1")
      case False
      obtain nl1' where p1': "path f nl1'" and hd_nl1': "hd nl1' = hd nl1" and 
      l_nl1': "last nl1' = last nl1" and d_nl1': "distinct nl1'" 
      and s_nl1': "set nl1' \<subseteq> set nl1"
      using 1(1)[THEN allE[of _ nl1]] p1 unfolding nl by auto
      obtain nl2' where nl1': "nl1' = n1 # nl2'" using path_NE[OF p1'] hd_nl1'
      unfolding Cons by(cases nl1', auto)
      show ?thesis apply(intro exI[of _ "n # nl1'"]) unfolding nl proof safe
        show "path f (n # nl1')" unfolding nl1' 
        apply(rule path.Ind, metis nl1' p1')
        by (metis (lifting) Cons list.inject nl p1 p_nl path.simps path_NE)
      qed(insert l_nl1' Cons nl1' s_nl1' d_nl1' False, auto)
    next
      case True
      then obtain nl11 nl12 where nl1: "nl1 = nl11 @ n # nl12" 
      by (metis split_list) 
      have p12: "path f (n # nl12)" 
      apply(rule path_post_concat[of _ "n # nl11"]) using p_nl[unfolded nl nl1] by auto
      obtain nl12' where p1': "path f nl12'" and hd_nl12': "hd nl12' = n" and 
      l_nl12': "last nl12' = last (n # nl12)" and d_nl12': "distinct nl12'" 
      and s_nl12': "set nl12' \<subseteq> {n} \<union> set nl12"
      using 1(1)[THEN allE[of _ "n # nl12"]] p12 unfolding nl nl1 by auto
      thus ?thesis apply(intro exI[of _ nl12']) unfolding nl nl1 by auto
    qed
  qed
qed

lemma path_subtr: 
assumes f: "\<And> n. root (f n) = n"
and p: "path f nl"
shows "subtr (set nl) (f (last nl)) (f (hd nl))"
using p proof (induct rule: path.induct)
  case (Ind n1 nl n)  let ?ns1 = "insert n1 (set nl)"
  have "path f (n1 # nl)"
  and "subtr ?ns1 (f (last (n1 # nl))) (f n1)"
  and fn1: "Inr (f n1) \<in> cont (f n)" using Ind by simp_all
  hence fn1_flast:  "subtr (insert n ?ns1) (f (last (n1 # nl))) (f n1)"
  by (metis subset_insertI subtr_mono) 
  have 1: "last (n # n1 # nl) = last (n1 # nl)" by auto
  have "subtr (insert n ?ns1) (f (last (n1 # nl))) (f n)" 
  using f subtr.Step[OF _ fn1_flast fn1] by auto 
  thus ?case unfolding 1 by simp 
qed (metis f hd.simps last_ConsL last_in_set not_Cons_self2 subtr.Refl)

lemma reg_subtr_path_aux:
assumes f: "reg f tr" and n: "subtr ns tr1 tr"
shows "\<exists> nl. path f nl \<and> f (hd nl) = tr \<and> f (last nl) = tr1 \<and> set nl \<subseteq> ns"
using n f proof(induct rule: subtr.induct)
  case (Refl tr ns)
  thus ?case
  apply(intro exI[of _ "[root tr]"]) apply simp by (metis (lifting) path.Base reg_root)
next
  case (Step tr ns tr2 tr1)
  hence rtr: "root tr \<in> ns" and tr1_tr: "Inr tr1 \<in> cont tr" 
  and tr2_tr1: "subtr ns tr2 tr1" and tr: "reg f tr" by auto
  have tr1: "reg f tr1" using reg_subtr[OF tr] rtr tr1_tr
  by (metis (lifting) Step.prems iso_tuple_UNIV_I reg_def subtr.Step)
  obtain nl where nl: "path f nl" and f_nl: "f (hd nl) = tr1" 
  and last_nl: "f (last nl) = tr2" and set: "set nl \<subseteq> ns" using Step(3)[OF tr1] by auto
  have 0: "path f (root tr # nl)" apply (subst path.simps)
  using f_nl nl reg_root tr tr1_tr by (metis hd.simps neq_Nil_conv) 
  show ?case apply(rule exI[of _ "(root tr) # nl"])
  using 0 reg_root tr last_nl nl path_NE rtr set by auto
qed 

lemma reg_subtr_path:
assumes f: "reg f tr" and n: "subtr ns tr1 tr"
shows "\<exists> nl. distinct nl \<and> path f nl \<and> f (hd nl) = tr \<and> f (last nl) = tr1 \<and> set nl \<subseteq> ns"
using reg_subtr_path_aux[OF assms] path_distinct[of f]
by (metis (lifting) order_trans)

lemma subtr_iff_path:
assumes r: "reg f tr" and f: "\<And> n. root (f n) = n"
shows "subtr ns tr1 tr \<longleftrightarrow> 
       (\<exists> nl. distinct nl \<and> path f nl \<and> f (hd nl) = tr \<and> f (last nl) = tr1 \<and> set nl \<subseteq> ns)"
proof safe
  fix nl assume p: "path f nl" and nl: "set nl \<subseteq> ns"
  have "subtr (set nl) (f (last nl)) (f (hd nl))"
  apply(rule path_subtr) using p f by simp_all
  thus "subtr ns (f (last nl)) (f (hd nl))"
  using subtr_mono nl by auto
qed(insert reg_subtr_path[OF r], auto)

lemma inFr_iff_path:
assumes r: "reg f tr" and f: "\<And> n. root (f n) = n"
shows 
"inFr ns tr t \<longleftrightarrow> 
 (\<exists> nl tr1. distinct nl \<and> path f nl \<and> f (hd nl) = tr \<and> f (last nl) = tr1 \<and> 
            set nl \<subseteq> ns \<and> Inl t \<in> cont tr1)" 
apply safe
apply (metis (no_types) inFr_subtr r reg_subtr_path)
by (metis f inFr.Base path_subtr subtr_inFr subtr_mono subtr_rootL_in)



subsection{* The regular cut of a tree *}

context fixes tr0 :: Tree
begin

(* Picking a subtree of a certain root: *)
definition "pick n \<equiv> SOME tr. subtr UNIV tr tr0 \<and> root tr = n" 

lemma pick:
assumes "inItr UNIV tr0 n"
shows "subtr UNIV (pick n) tr0 \<and> root (pick n) = n"
proof-
  have "\<exists> tr. subtr UNIV tr tr0 \<and> root tr = n" 
  using assms by (metis (lifting) inItr_subtr)
  thus ?thesis unfolding pick_def by(rule someI_ex)
qed 

lemmas subtr_pick = pick[THEN conjunct1]
lemmas root_pick = pick[THEN conjunct2]

lemma dtree_pick:
assumes tr0: "dtree tr0" and n: "inItr UNIV tr0 n" 
shows "dtree (pick n)"
using dtree_subtr[OF tr0 subtr_pick[OF n]] .

definition "regOf_r n \<equiv> root (pick n)"
definition "regOf_c n \<equiv> (id \<oplus> root) ` cont (pick n)"

(* The regular tree of a function: *)
definition regOf :: "N \<Rightarrow> Tree" where  
"regOf \<equiv> coit regOf_r regOf_c"

lemma finite_regOf_c: "finite (regOf_c n)"
unfolding regOf_c_def by (metis finite_cont finite_imageI) 

lemma root_regOf_pick: "root (regOf n) = root (pick n)"
using coit(1)[of regOf_r regOf_c n] unfolding regOf_def regOf_r_def by simp

lemma root_regOf[simp]: 
assumes "inItr UNIV tr0 n"
shows "root (regOf n) = n"
unfolding root_regOf_pick root_pick[OF assms] ..

lemma cont_regOf[simp]: 
"cont (regOf n) = (id \<oplus> (regOf o root)) ` cont (pick n)"
apply(subst id_o[symmetric, of id]) unfolding sum_map.comp[symmetric]
unfolding image_compose unfolding regOf_c_def[symmetric]
using coit(2)[of regOf_c n regOf_r, OF finite_regOf_c] 
unfolding regOf_def ..

lemma Inl_cont_regOf[simp]:
"Inl -` (cont (regOf n)) = Inl -` (cont (pick n))" 
unfolding cont_regOf by simp

lemma Inr_cont_regOf:
"Inr -` (cont (regOf n)) = (regOf \<circ> root) ` (Inr -` cont (pick n))"
unfolding cont_regOf by simp

lemma subtr_regOf: 
assumes n: "inItr UNIV tr0 n" and "subtr UNIV tr1 (regOf n)"
shows "\<exists> n1. inItr UNIV tr0 n1 \<and> tr1 = regOf n1"
proof-
  {fix tr ns assume "subtr UNIV tr1 tr"
   hence "tr = regOf n \<longrightarrow> (\<exists> n1. inItr UNIV tr0 n1 \<and> tr1 = regOf n1)"
   proof (induct rule: subtr_UNIV_inductL) 
     case (Step tr2 tr1 tr) 
     show ?case proof
       assume "tr = regOf n"
       then obtain n1 where tr2: "Inr tr2 \<in> cont tr1"
       and tr1_tr: "subtr UNIV tr1 tr" and n1: "inItr UNIV tr0 n1" and tr1: "tr1 = regOf n1"
       using Step by auto
       obtain tr2' where tr2: "tr2 = regOf (root tr2')" 
       and tr2': "Inr tr2' \<in> cont (pick n1)"
       using tr2 Inr_cont_regOf[of n1] 
       unfolding tr1 image_def o_def using vimage_eq by auto
       have "inItr UNIV tr0 (root tr2')" 
       using inItr.Base inItr.Ind n1 pick subtr_inItr tr2' by (metis iso_tuple_UNIV_I)
       thus "\<exists>n2. inItr UNIV tr0 n2 \<and> tr2 = regOf n2" using tr2 by blast
     qed
   qed(insert n, auto)
  }
  thus ?thesis using assms by auto
qed

lemma root_regOf_root: 
assumes n: "inItr UNIV tr0 n" and t_tr: "t_tr \<in> cont (pick n)"
shows "(id \<oplus> (root \<circ> regOf \<circ> root)) t_tr = (id \<oplus> root) t_tr"
using assms apply(cases t_tr)
  apply (metis (lifting) sum_map.simps(1))
  using pick regOf_def regOf_r_def coit(1) 
      inItr.Base o_apply subtr_StepL subtr_inItr sum_map.simps(2)
  by (metis UNIV_I)

lemma regOf_P: 
assumes tr0: "dtree tr0" and n: "inItr UNIV tr0 n" 
shows "(n, (id \<oplus> root) ` cont (regOf n)) \<in> P" (is "?L \<in> P")
proof- 
  have "?L = (n, (id \<oplus> root) ` cont (pick n))"
  unfolding cont_regOf image_compose[symmetric] sum_map.comp id_o o_assoc
  unfolding Pair_eq apply(rule conjI[OF refl]) apply(rule image_cong[OF refl])
  by(rule root_regOf_root[OF n])
  moreover have "... \<in> P" by (metis (lifting) dtree_pick root_pick dtree_P n tr0) 
  ultimately show ?thesis by simp
qed

lemma dtree_regOf:
assumes tr0: "dtree tr0" and "inItr UNIV tr0 n" 
shows "dtree (regOf n)"
proof-
  {fix tr have "\<exists> n. inItr UNIV tr0 n \<and> tr = regOf n \<Longrightarrow> dtree tr" 
   proof (induct rule: dtree_raw_coind)
     case (Hyp tr) 
     then obtain n where n: "inItr UNIV tr0 n" and tr: "tr = regOf n" by auto
     show ?case unfolding lift_def apply safe
     apply (metis (lifting) regOf_P root_regOf n tr tr0)
     unfolding tr Inr_cont_regOf unfolding inj_on_def apply clarsimp using root_regOf 
     apply (metis UNIV_I inItr.Base n pick subtr2.simps subtr_inItr subtr_subtr2)
     by (metis n subtr.Refl subtr_StepL subtr_regOf tr UNIV_I)
   qed   
  }
  thus ?thesis using assms by blast
qed

(* The regular cut of a tree: *)   
definition "rcut \<equiv> regOf (root tr0)"

theorem reg_rcut: "reg regOf rcut"
unfolding reg_def rcut_def 
by (metis inItr.Base root_regOf subtr_regOf UNIV_I) 

lemma rcut_reg:
assumes "reg regOf tr0" 
shows "rcut = tr0"
using assms unfolding rcut_def reg_def by (metis subtr.Refl UNIV_I)

theorem rcut_eq: "rcut = tr0 \<longleftrightarrow> reg regOf tr0"
using reg_rcut rcut_reg by metis

theorem regular_rcut: "regular rcut"
using reg_rcut unfolding regular_def by blast

theorem Fr_rcut: "Fr UNIV rcut \<subseteq> Fr UNIV tr0"
proof safe
  fix t assume "t \<in> Fr UNIV rcut"
  then obtain tr where t: "Inl t \<in> cont tr" and tr: "subtr UNIV tr (regOf (root tr0))"
  using Fr_subtr[of UNIV "regOf (root tr0)"] unfolding rcut_def
  by (metis (full_types) Fr_def inFr_subtr mem_Collect_eq) 
  obtain n where n: "inItr UNIV tr0 n" and tr: "tr = regOf n" using tr
  by (metis (lifting) inItr.Base subtr_regOf UNIV_I)
  have "Inl t \<in> cont (pick n)" using t using Inl_cont_regOf[of n] unfolding tr
  by (metis (lifting) vimageD vimageI2) 
  moreover have "subtr UNIV (pick n) tr0" using subtr_pick[OF n] ..
  ultimately show "t \<in> Fr UNIV tr0" unfolding Fr_subtr_cont by auto
qed

theorem dtree_rcut: 
assumes "dtree tr0"
shows "dtree rcut" 
unfolding rcut_def using dtree_regOf[OF assms inItr.Base] by simp

theorem root_rcut[simp]: "root rcut = root tr0" 
unfolding rcut_def
by (metis (lifting) root_regOf inItr.Base reg_def reg_root subtr_rootR_in) 

end (* context *)


subsection{* Recursive description of the regular tree frontiers *} 

lemma regular_inFr:
assumes r: "regular tr" and In: "root tr \<in> ns"
and t: "inFr ns tr t"
shows "t \<in> Inl -` (cont tr) \<or> 
       (\<exists> tr'. Inr tr' \<in> cont tr \<and> inFr (ns - {root tr}) tr' t)"
(is "?L \<or> ?R")
proof-
  obtain f where r: "reg f tr" and f: "\<And>n. root (f n) = n" 
  using r unfolding regular_def2 by auto
  obtain nl tr1 where d_nl: "distinct nl" and p: "path f nl" and hd_nl: "f (hd nl) = tr" 
  and l_nl: "f (last nl) = tr1" and s_nl: "set nl \<subseteq> ns" and t_tr1: "Inl t \<in> cont tr1" 
  using t unfolding inFr_iff_path[OF r f] by auto
  obtain n nl1 where nl: "nl = n # nl1" by (metis (lifting) p path.simps) 
  hence f_n: "f n = tr" using hd_nl by simp
  have n_nl1: "n \<notin> set nl1" using d_nl unfolding nl by auto
  show ?thesis
  proof(cases nl1)
    case Nil hence "tr = tr1" using f_n l_nl unfolding nl by simp
    hence ?L using t_tr1 by simp thus ?thesis by simp
  next
    case (Cons n1 nl2) note nl1 = Cons
    have 1: "last nl1 = last nl" "hd nl1 = n1" unfolding nl nl1 by simp_all
    have p1: "path f nl1" and n1_tr: "Inr (f n1) \<in> cont tr" 
    using path.simps[of f nl] p f_n unfolding nl nl1 by auto
    have r1: "reg f (f n1)" using reg_Inr_cont[OF r n1_tr] .
    have 0: "inFr (set nl1) (f n1) t" unfolding inFr_iff_path[OF r1 f]
    apply(intro exI[of _ nl1], intro exI[of _ tr1])
    using d_nl unfolding 1 l_nl unfolding nl using p1 t_tr1 by auto
    have root_tr: "root tr = n" by (metis f f_n) 
    have "inFr (ns - {root tr}) (f n1) t" apply(rule inFr_mono[OF 0])
    using s_nl unfolding root_tr unfolding nl using n_nl1 by auto
    thus ?thesis using n1_tr by auto
  qed
qed
 
theorem regular_Fr: 
assumes r: "regular tr" and In: "root tr \<in> ns"
shows "Fr ns tr = 
       Inl -` (cont tr) \<union> 
       \<Union> {Fr (ns - {root tr}) tr' | tr'. Inr tr' \<in> cont tr}"
unfolding Fr_def 
using In inFr.Base regular_inFr[OF assms] apply safe
apply (simp, metis (full_types) UnionI mem_Collect_eq)
apply simp
by (simp, metis (lifting) inFr_Ind_minus insert_Diff)


subsection{* The generated languages *} 

(* The (possibly inifinite tree) generated language *)
definition "L ns n \<equiv> {Fr ns tr | tr. dtree tr \<and> root tr = n}"

(* The regular-tree generated language *)
definition "Lr ns n \<equiv> {Fr ns tr | tr. dtree tr \<and> root tr = n \<and> regular tr}"

theorem L_rec_notin:
assumes "n \<notin> ns"
shows "L ns n = {{}}"
using assms unfolding L_def apply safe 
  using not_root_Fr apply force
  apply(rule exI[of _ "deftr n"])
  by (metis (no_types) dtree_deftr not_root_Fr root_deftr)

theorem Lr_rec_notin:
assumes "n \<notin> ns"
shows "Lr ns n = {{}}"
using assms unfolding Lr_def apply safe
  using not_root_Fr apply force
  apply(rule exI[of _ "deftr n"])
  by (metis (no_types) regular_def dtree_deftr not_root_Fr reg_deftr root_deftr)

lemma dtree_subtrOf: 
assumes "dtree tr" and "Inr n \<in> prodOf tr"
shows "dtree (subtrOf tr n)"
by (metis assms dtree_lift lift_def subtrOf) 
  
theorem Lr_rec_in: 
assumes n: "n \<in> ns"
shows "Lr ns n \<subseteq> 
{Inl -` tns \<union> (\<Union> {K n' | n'. Inr n' \<in> tns}) | tns K. 
    (n,tns) \<in> P \<and> 
    (\<forall> n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> Lr (ns - {n}) n')}"
(is "Lr ns n \<subseteq> {?F tns K | tns K. (n,tns) \<in> P \<and> ?\<phi> tns K}")
proof safe
  fix ts assume "ts \<in> Lr ns n"
  then obtain tr where dtr: "dtree tr" and r: "root tr = n" and tr: "regular tr"
  and ts: "ts = Fr ns tr" unfolding Lr_def by auto
  def tns \<equiv> "(id \<oplus> root) ` (cont tr)"
  def K \<equiv> "\<lambda> n'. Fr (ns - {n}) (subtrOf tr n')"
  show "\<exists>tns K. ts = ?F tns K \<and> (n, tns) \<in> P \<and> ?\<phi> tns K"
  apply(rule exI[of _ tns], rule exI[of _ K]) proof(intro conjI allI impI)
    show "ts = Inl -` tns \<union> \<Union>{K n' |n'. Inr n' \<in> tns}"
    unfolding ts regular_Fr[OF tr n[unfolded r[symmetric]]]
    unfolding tns_def K_def r[symmetric]
    unfolding Inl_prodOf dtree_subtrOf_Union[OF dtr] ..
    show "(n, tns) \<in> P" unfolding tns_def r[symmetric] using dtree_P[OF dtr] .
    fix n' assume "Inr n' \<in> tns" thus "K n' \<in> Lr (ns - {n}) n'"
    unfolding K_def Lr_def mem_Collect_eq apply(intro exI[of _ "subtrOf tr n'"])
    using dtr tr apply(intro conjI refl)  unfolding tns_def
      apply(erule dtree_subtrOf[OF dtr])
      apply (metis subtrOf)
      by (metis Inr_subtrOf UNIV_I regular_subtr subtr.simps)
  qed
qed 

lemma hsubst_aux: 
fixes n ftr tns
assumes n: "n \<in> ns" and tns: "finite tns" and 
1: "\<And> n'. Inr n' \<in> tns \<Longrightarrow> dtree (ftr n')"
defines "tr \<equiv> Node n ((id \<oplus> ftr) ` tns)"  defines "tr' \<equiv> hsubst tr tr"
shows "Fr ns tr' = Inl -` tns \<union> \<Union>{Fr (ns - {n}) (ftr n') |n'. Inr n' \<in> tns}"
(is "_ = ?B") proof-
  have rtr: "root tr = n" and ctr: "cont tr = (id \<oplus> ftr) ` tns"
  unfolding tr_def using tns by auto
  have Frr: "Frr (ns - {n}) tr = \<Union>{Fr (ns - {n}) (ftr n') |n'. Inr n' \<in> tns}"
  unfolding Frr_def ctr by auto
  have "Fr ns tr' = Inl -` (cont tr) \<union> Frr (ns - {n}) tr"
  using Fr_self_hsubst[OF n[unfolded rtr[symmetric]]] unfolding tr'_def rtr ..
  also have "... = ?B" unfolding ctr Frr by simp
  finally show ?thesis .
qed

theorem L_rec_in: 
assumes n: "n \<in> ns"
shows "
{Inl -` tns \<union> (\<Union> {K n' | n'. Inr n' \<in> tns}) | tns K. 
    (n,tns) \<in> P \<and> 
    (\<forall> n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> L (ns - {n}) n')} 
 \<subseteq> L ns n"
proof safe
  fix tns K
  assume P: "(n, tns) \<in> P" and 0: "\<forall>n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> L (ns - {n}) n'"
  {fix n' assume "Inr n' \<in> tns"
   hence "K n' \<in> L (ns - {n}) n'" using 0 by auto
   hence "\<exists> tr'. K n' = Fr (ns - {n}) tr' \<and> dtree tr' \<and> root tr' = n'"
   unfolding L_def mem_Collect_eq by auto
  }
  then obtain ftr where 0: "\<And> n'. Inr n' \<in> tns \<Longrightarrow>  
  K n' = Fr (ns - {n}) (ftr n') \<and> dtree (ftr n') \<and> root (ftr n') = n'"
  by metis
  def tr \<equiv> "Node n ((id \<oplus> ftr) ` tns)"  def tr' \<equiv> "hsubst tr tr"
  have rtr: "root tr = n" and ctr: "cont tr = (id \<oplus> ftr) ` tns"
  unfolding tr_def by (simp, metis P cont_Node finite_imageI finite_in_P)
  have prtr: "prodOf tr = tns" apply(rule Inl_Inr_image_cong) 
  unfolding ctr apply simp apply simp apply safe 
  using 0 unfolding image_def apply force apply simp by (metis 0 vimageI2)     
  have 1: "{K n' |n'. Inr n' \<in> tns} = {Fr (ns - {n}) (ftr n') |n'. Inr n' \<in> tns}"
  using 0 by auto
  have dtr: "dtree tr" apply(rule dtree.Tree)
    apply (metis (lifting) P prtr rtr) 
    unfolding inj_on_def ctr lift_def using 0 by auto
  hence dtr': "dtree tr'" unfolding tr'_def by (metis dtree_hsubst)
  have tns: "finite tns" using finite_in_P P by simp
  have "Inl -` tns \<union> \<Union>{Fr (ns - {n}) (ftr n') |n'. Inr n' \<in> tns} \<in> L ns n"
  unfolding L_def mem_Collect_eq apply(intro exI[of _ tr'] conjI)
  using dtr' 0 hsubst_aux[OF assms tns, of ftr] unfolding tr_def tr'_def by auto
  thus "Inl -` tns \<union> \<Union>{K n' |n'. Inr n' \<in> tns} \<in> L ns n" unfolding 1 .
qed

lemma card_N: "(n::N) \<in> ns \<Longrightarrow> card (ns - {n}) < card ns" 
by (metis finite_N Diff_UNIV Diff_infinite_finite card_Diff1_less finite.emptyI)

function LL where 
"LL ns n = 
 (if n \<notin> ns then {{}} else 
 {Inl -` tns \<union> (\<Union> {K n' | n'. Inr n' \<in> tns}) | tns K. 
    (n,tns) \<in> P \<and> 
    (\<forall> n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> LL (ns - {n}) n')})"
by(pat_completeness, auto)
termination apply(relation "inv_image (measure card) fst") 
using card_N by auto

declare LL.simps[code]  (* TODO: Does code generation for LL work? *)
declare LL.simps[simp del]

theorem Lr_LL: "Lr ns n \<subseteq> LL ns n" 
proof (induct ns arbitrary: n rule: measure_induct[of card]) 
  case (1 ns n) show ?case proof(cases "n \<in> ns")
    case False thus ?thesis unfolding Lr_rec_notin[OF False] by (simp add: LL.simps)
  next
    case True show ?thesis apply(rule subset_trans)
    using Lr_rec_in[OF True] apply assumption 
    unfolding LL.simps[of ns n] using True 1 card_N proof clarsimp
      fix tns K
      assume "n \<in> ns" hence c: "card (ns - {n}) < card ns" using card_N by blast
      assume "(n, tns) \<in> P" 
      and "\<forall>n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> Lr (ns - {n}) n'"
      thus "\<exists>tnsa Ka.
             Inl -` tns \<union> \<Union>{K n' |n'. Inr n' \<in> tns} =
             Inl -` tnsa \<union> \<Union>{Ka n' |n'. Inr n' \<in> tnsa} \<and>
             (n, tnsa) \<in> P \<and> (\<forall>n'. Inr n' \<in> tnsa \<longrightarrow> Ka n' \<in> LL (ns - {n}) n')"
      apply(intro exI[of _ tns] exI[of _ K]) using c 1 by auto
    qed
  qed
qed

theorem LL_L: "LL ns n \<subseteq> L ns n" 
proof (induct ns arbitrary: n rule: measure_induct[of card]) 
  case (1 ns n) show ?case proof(cases "n \<in> ns")
    case False thus ?thesis unfolding L_rec_notin[OF False] by (simp add: LL.simps)
  next
    case True show ?thesis apply(rule subset_trans)
    prefer 2 using L_rec_in[OF True] apply assumption 
    unfolding LL.simps[of ns n] using True 1 card_N proof clarsimp
      fix tns K
      assume "n \<in> ns" hence c: "card (ns - {n}) < card ns" using card_N by blast
      assume "(n, tns) \<in> P" 
      and "\<forall>n'. Inr n' \<in> tns \<longrightarrow> K n' \<in> LL (ns - {n}) n'"
      thus "\<exists>tnsa Ka.
             Inl -` tns \<union> \<Union>{K n' |n'. Inr n' \<in> tns} =
             Inl -` tnsa \<union> \<Union>{Ka n' |n'. Inr n' \<in> tnsa} \<and>
             (n, tnsa) \<in> P \<and> (\<forall>n'. Inr n' \<in> tnsa \<longrightarrow> Ka n' \<in> L (ns - {n}) n')"
      apply(intro exI[of _ tns] exI[of _ K]) using c 1 by auto
    qed
  qed
qed

(* The subsumpsion relation between languages *)
definition "subs L1 L2 \<equiv> \<forall> ts2 \<in> L2. \<exists> ts1 \<in> L1. ts1 \<subseteq> ts2"

lemma incl_subs[simp]: "L2 \<subseteq> L1 \<Longrightarrow> subs L1 L2"
unfolding subs_def by auto

lemma subs_refl[simp]: "subs L1 L1" unfolding subs_def by auto

lemma subs_trans: "\<lbrakk>subs L1 L2; subs L2 L3\<rbrakk> \<Longrightarrow> subs L1 L3" 
unfolding subs_def by (metis subset_trans) 

(* Language equivalence *)
definition "leqv L1 L2 \<equiv> subs L1 L2 \<and> subs L2 L1"

lemma subs_leqv[simp]: "leqv L1 L2 \<Longrightarrow> subs L1 L2"
unfolding leqv_def by auto

lemma subs_leqv_sym[simp]: "leqv L1 L2 \<Longrightarrow> subs L2 L1"
unfolding leqv_def by auto

lemma leqv_refl[simp]: "leqv L1 L1" unfolding leqv_def by auto

lemma leqv_trans: 
assumes 12: "leqv L1 L2" and 23: "leqv L2 L3"
shows "leqv L1 L3"
using assms unfolding leqv_def by (metis (lifting) subs_trans) 

lemma leqv_sym: "leqv L1 L2 \<Longrightarrow> leqv L2 L1"
unfolding leqv_def by auto

lemma leqv_Sym: "leqv L1 L2 \<longleftrightarrow> leqv L2 L1"
unfolding leqv_def by auto

lemma Lr_incl_L: "Lr ns ts \<subseteq> L ns ts"
unfolding Lr_def L_def by auto

lemma Lr_subs_L: "subs (Lr UNIV ts) (L UNIV ts)"
unfolding subs_def proof safe
  fix ts2 assume "ts2 \<in> L UNIV ts"
  then obtain tr where ts2: "ts2 = Fr UNIV tr" and dtr: "dtree tr" and rtr: "root tr = ts" 
  unfolding L_def by auto
  thus "\<exists>ts1\<in>Lr UNIV ts. ts1 \<subseteq> ts2"
  apply(intro bexI[of _ "Fr UNIV (rcut tr)"])
  unfolding Lr_def L_def using Fr_rcut dtree_rcut root_rcut regular_rcut by auto
qed

theorem Lr_leqv_L: "leqv (Lr UNIV ts) (L UNIV ts)"
using Lr_subs_L unfolding leqv_def by (metis (lifting) Lr_incl_L incl_subs)

theorem LL_leqv_L: "leqv (LL UNIV ts) (L UNIV ts)"
by (metis (lifting) LL_L Lr_LL Lr_subs_L incl_subs leqv_def subs_trans)

theorem LL_leqv_Lr: "leqv (LL UNIV ts) (Lr UNIV ts)"
using Lr_leqv_L LL_leqv_L by (metis leqv_Sym leqv_trans)


end
