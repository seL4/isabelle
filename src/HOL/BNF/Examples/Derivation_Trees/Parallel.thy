(*  Title:      HOL/BNF/Examples/Derivation_Trees/Parallel.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Parallel composition.
*)

header {* Parallel Composition *}

theory Parallel
imports DTree
begin

no_notation plus_class.plus (infixl "+" 65)
no_notation Sublist.parallel (infixl "\<parallel>" 50)

consts Nplus :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+" 60)

axiomatization where
    Nplus_comm: "(a::N) + b = b + (a::N)"
and Nplus_assoc: "((a::N) + b) + c = a + (b + c)"

subsection{* Corecursive Definition of Parallel Composition *}

fun par_r where "par_r (tr1,tr2) = root tr1 + root tr2"
fun par_c where
"par_c (tr1,tr2) =
 Inl ` (Inl -` (cont tr1 \<union> cont tr2)) \<union>
 Inr ` (Inr -` cont tr1 \<times> Inr -` cont tr2)"

declare par_r.simps[simp del]  declare par_c.simps[simp del]

definition par :: "dtree \<times> dtree \<Rightarrow> dtree" where
"par \<equiv> unfold par_r par_c"

abbreviation par_abbr (infixr "\<parallel>" 80) where "tr1 \<parallel> tr2 \<equiv> par (tr1, tr2)"

lemma finite_par_c: "finite (par_c (tr1, tr2))"
unfolding par_c.simps apply(rule finite_UnI)
  apply (metis finite_Un finite_cont finite_imageI finite_vimageI inj_Inl)
  apply(intro finite_imageI finite_cartesian_product finite_vimageI)
  using finite_cont by auto

lemma root_par: "root (tr1 \<parallel> tr2) = root tr1 + root tr2"
using unfold(1)[of par_r par_c "(tr1,tr2)"] unfolding par_def par_r.simps by simp

lemma cont_par:
"cont (tr1 \<parallel> tr2) = (id \<oplus> par) ` par_c (tr1,tr2)"
using unfold(2)[of par_c "(tr1,tr2)" par_r, OF finite_par_c]
unfolding par_def ..

lemma Inl_cont_par[simp]:
"Inl -` (cont (tr1 \<parallel> tr2)) = Inl -` (cont tr1 \<union> cont tr2)"
unfolding cont_par par_c.simps by auto

lemma Inr_cont_par[simp]:
"Inr -` (cont (tr1 \<parallel> tr2)) = par ` (Inr -` cont tr1 \<times> Inr -` cont tr2)"
unfolding cont_par par_c.simps by auto

lemma Inl_in_cont_par:
"Inl t \<in> cont (tr1 \<parallel> tr2) \<longleftrightarrow> (Inl t \<in> cont tr1 \<or> Inl t \<in> cont tr2)"
using Inl_cont_par[of tr1 tr2] unfolding vimage_def by auto

lemma Inr_in_cont_par:
"Inr t \<in> cont (tr1 \<parallel> tr2) \<longleftrightarrow> (t \<in> par ` (Inr -` cont tr1 \<times> Inr -` cont tr2))"
using Inr_cont_par[of tr1 tr2] unfolding vimage_def by auto


subsection{* Structural Coinduction Proofs *}

lemma set_rel_sum_rel_eq[simp]:
"set_rel (sum_rel (op =) \<phi>) A1 A2 \<longleftrightarrow>
 Inl -` A1 = Inl -` A2 \<and> set_rel \<phi> (Inr -` A1) (Inr -` A2)"
unfolding set_rel_sum_rel set_rel_eq ..

(* Detailed proofs of commutativity and associativity: *)
theorem par_com: "tr1 \<parallel> tr2 = tr2 \<parallel> tr1"
proof-
  let ?\<theta> = "\<lambda> trA trB. \<exists> tr1 tr2. trA = tr1 \<parallel> tr2 \<and> trB = tr2 \<parallel> tr1"
  {fix trA trB
   assume "?\<theta> trA trB" hence "trA = trB"
   apply (induct rule: dtree_coinduct)
   unfolding set_rel_sum_rel set_rel_eq unfolding set_rel_def proof safe
     fix tr1 tr2  show "root (tr1 \<parallel> tr2) = root (tr2 \<parallel> tr1)"
     unfolding root_par by (rule Nplus_comm)
   next
     fix n tr1 tr2 assume "Inl n \<in> cont (tr1 \<parallel> tr2)" thus "n \<in> Inl -` (cont (tr2 \<parallel> tr1))"
     unfolding Inl_in_cont_par by auto
   next
     fix n tr1 tr2 assume "Inl n \<in> cont (tr2 \<parallel> tr1)" thus "n \<in> Inl -` (cont (tr1 \<parallel> tr2))"
     unfolding Inl_in_cont_par by auto
   next
     fix tr1 tr2 trA' assume "Inr trA' \<in> cont (tr1 \<parallel> tr2)"
     then obtain tr1' tr2' where "trA' = tr1' \<parallel> tr2'"
     and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
     unfolding Inr_in_cont_par by auto
     thus "\<exists> trB' \<in> Inr -` (cont (tr2 \<parallel> tr1)). ?\<theta> trA' trB'"
     apply(intro bexI[of _ "tr2' \<parallel> tr1'"]) unfolding Inr_in_cont_par by auto
   next
     fix tr1 tr2 trB' assume "Inr trB' \<in> cont (tr2 \<parallel> tr1)"
     then obtain tr1' tr2' where "trB' = tr2' \<parallel> tr1'"
     and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
     unfolding Inr_in_cont_par by auto
     thus "\<exists> trA' \<in> Inr -` (cont (tr1 \<parallel> tr2)). ?\<theta> trA' trB'"
     apply(intro bexI[of _ "tr1' \<parallel> tr2'"]) unfolding Inr_in_cont_par by auto
   qed
  }
  thus ?thesis by blast
qed

lemma par_assoc: "(tr1 \<parallel> tr2) \<parallel> tr3 = tr1 \<parallel> (tr2 \<parallel> tr3)"
proof-
  let ?\<theta> =
  "\<lambda> trA trB. \<exists> tr1 tr2 tr3. trA = (tr1 \<parallel> tr2) \<parallel> tr3 \<and> trB = tr1 \<parallel> (tr2 \<parallel> tr3)"
  {fix trA trB
   assume "?\<theta> trA trB" hence "trA = trB"
   apply (induct rule: dtree_coinduct)
   unfolding set_rel_sum_rel set_rel_eq unfolding set_rel_def proof safe
     fix tr1 tr2 tr3  show "root ((tr1 \<parallel> tr2) \<parallel> tr3) = root (tr1 \<parallel> (tr2 \<parallel> tr3))"
     unfolding root_par by (rule Nplus_assoc)
   next
     fix n tr1 tr2 tr3 assume "Inl n \<in> (cont ((tr1 \<parallel> tr2) \<parallel> tr3))"
     thus "n \<in> Inl -` (cont (tr1 \<parallel> tr2 \<parallel> tr3))" unfolding Inl_in_cont_par by simp
   next
     fix n tr1 tr2 tr3 assume "Inl n \<in> (cont (tr1 \<parallel> tr2 \<parallel> tr3))"
     thus "n \<in> Inl -` (cont ((tr1 \<parallel> tr2) \<parallel> tr3))" unfolding Inl_in_cont_par by simp
   next
     fix trA' tr1 tr2 tr3 assume "Inr trA' \<in> cont ((tr1 \<parallel> tr2) \<parallel> tr3)"
     then obtain tr1' tr2' tr3' where "trA' = (tr1' \<parallel> tr2') \<parallel> tr3'"
     and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
     and "Inr tr3' \<in> cont tr3" unfolding Inr_in_cont_par by auto
     thus "\<exists> trB' \<in> Inr -` (cont (tr1 \<parallel> tr2 \<parallel> tr3)). ?\<theta> trA' trB'"
     apply(intro bexI[of _ "tr1' \<parallel> tr2' \<parallel> tr3'"])
     unfolding Inr_in_cont_par by auto
   next
     fix trB' tr1 tr2 tr3 assume "Inr trB' \<in> cont (tr1 \<parallel> tr2 \<parallel> tr3)"
     then obtain tr1' tr2' tr3' where "trB' = tr1' \<parallel> (tr2' \<parallel> tr3')"
     and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
     and "Inr tr3' \<in> cont tr3" unfolding Inr_in_cont_par by auto
     thus "\<exists> trA' \<in> Inr -` cont ((tr1 \<parallel> tr2) \<parallel> tr3). ?\<theta> trA' trB'"
     apply(intro bexI[of _ "(tr1' \<parallel> tr2') \<parallel> tr3'"])
     unfolding Inr_in_cont_par by auto
   qed
  }
  thus ?thesis by blast
qed

end