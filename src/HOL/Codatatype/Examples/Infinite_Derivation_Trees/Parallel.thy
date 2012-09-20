(*  Title:      HOL/Codatatype/Examples/Infinite_Derivation_Trees/Parallel.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Parallel composition.
*)

header {* Parallel Composition *}

theory Parallel 
imports Tree
begin


consts Nplus :: "N \<Rightarrow> N \<Rightarrow> N" (infixl "+" 60)

axiomatization where 
    Nplus_comm: "(a::N) + b = b + (a::N)"
and Nplus_assoc: "((a::N) + b) + c = a + (b + c)"



section{* Parallel composition *} 

fun par_r where "par_r (tr1,tr2) = root tr1 + root tr2"
fun par_c where 
"par_c (tr1,tr2) = 
 Inl ` (Inl -` (cont tr1 \<union> cont tr2)) \<union> 
 Inr ` (Inr -` cont tr1 \<times> Inr -` cont tr2)"

declare par_r.simps[simp del]  declare par_c.simps[simp del]

definition par :: "Tree \<times> Tree \<Rightarrow> Tree" where  
"par \<equiv> coit par_r par_c"

abbreviation par_abbr (infixr "\<parallel>" 80) where "tr1 \<parallel> tr2 \<equiv> par (tr1, tr2)"

lemma finite_par_c: "finite (par_c (tr1, tr2))"
unfolding par_c.simps apply(rule finite_UnI)
  apply (metis finite_Un finite_cont finite_imageI finite_vimageI inj_Inl)
  apply(intro finite_imageI finite_cartesian_product finite_vimageI)
  using finite_cont by auto

lemma root_par: "root (tr1 \<parallel> tr2) = root tr1 + root tr2"
using coit(1)[of par_r par_c "(tr1,tr2)"] unfolding par_def par_r.simps by simp

lemma cont_par: 
"cont (tr1 \<parallel> tr2) = (id \<oplus> par) ` par_c (tr1,tr2)"
using coit(2)[of par_c "(tr1,tr2)" par_r, OF finite_par_c]
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


section{* =-coinductive proofs *}

(* Detailed proofs of commutativity and associativity: *)
theorem par_com: "tr1 \<parallel> tr2 = tr2 \<parallel> tr1"
proof-
  let ?\<phi> = "\<lambda> trA trB. \<exists> tr1 tr2. trA = tr1 \<parallel> tr2 \<and> trB = tr2 \<parallel> tr1"
  {fix trA trB
   assume "?\<phi> trA trB" hence "trA = trB"
   proof (induct rule: Tree_coind, safe)
     fix tr1 tr2 
     show "root (tr1 \<parallel> tr2) = root (tr2 \<parallel> tr1)" 
     unfolding root_par by (rule Nplus_comm)
   next
     fix tr1 tr2 :: Tree
     let ?trA = "tr1 \<parallel> tr2"  let ?trB = "tr2 \<parallel> tr1"
     show "(?\<phi> ^#2) (cont ?trA) (cont ?trB)"
     unfolding lift2_def proof(intro conjI allI impI)
       fix n show "Inl n \<in> cont (tr1 \<parallel> tr2) \<longleftrightarrow> Inl n \<in> cont (tr2 \<parallel> tr1)"
       unfolding Inl_in_cont_par by auto
     next
       fix trA' assume "Inr trA' \<in> cont ?trA"
       then obtain tr1' tr2' where "trA' = tr1' \<parallel> tr2'"
       and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
       unfolding Inr_in_cont_par by auto
       thus "\<exists> trB'. Inr trB' \<in> cont ?trB \<and> ?\<phi> trA' trB'"
       apply(intro exI[of _ "tr2' \<parallel> tr1'"]) unfolding Inr_in_cont_par by auto
     next
       fix trB' assume "Inr trB' \<in> cont ?trB"
       then obtain tr1' tr2' where "trB' = tr2' \<parallel> tr1'"
       and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
       unfolding Inr_in_cont_par by auto
       thus "\<exists> trA'. Inr trA' \<in> cont ?trA \<and> ?\<phi> trA' trB'"
       apply(intro exI[of _ "tr1' \<parallel> tr2'"]) unfolding Inr_in_cont_par by auto
     qed
   qed
  }
  thus ?thesis by blast
qed

theorem par_assoc: "(tr1 \<parallel> tr2) \<parallel> tr3 = tr1 \<parallel> (tr2 \<parallel> tr3)"
proof-
  let ?\<phi> = 
  "\<lambda> trA trB. \<exists> tr1 tr2 tr3. trA = (tr1 \<parallel> tr2) \<parallel> tr3 \<and> 
                             trB = tr1 \<parallel> (tr2 \<parallel> tr3)"
  {fix trA trB
   assume "?\<phi> trA trB" hence "trA = trB"
   proof (induct rule: Tree_coind, safe)
     fix tr1 tr2 tr3 
     show "root ((tr1 \<parallel> tr2) \<parallel> tr3) = root (tr1 \<parallel> (tr2 \<parallel> tr3))" 
     unfolding root_par by (rule Nplus_assoc)
   next
     fix tr1 tr2 tr3 
     let ?trA = "(tr1 \<parallel> tr2) \<parallel> tr3"  let ?trB = "tr1 \<parallel> (tr2 \<parallel> tr3)"
     show "(?\<phi> ^#2) (cont ?trA) (cont ?trB)"
     unfolding lift2_def proof(intro conjI allI impI)
       fix n show "Inl n \<in> (cont ?trA) \<longleftrightarrow> Inl n \<in> (cont ?trB)"
       unfolding Inl_in_cont_par by simp
     next
       fix trA' assume "Inr trA' \<in> cont ?trA"
       then obtain tr1' tr2' tr3' where "trA' = (tr1' \<parallel> tr2') \<parallel> tr3'"
       and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
       and "Inr tr3' \<in> cont tr3" unfolding Inr_in_cont_par by auto
       thus "\<exists> trB'. Inr trB' \<in> cont ?trB \<and> ?\<phi> trA' trB'"
       apply(intro exI[of _ "tr1' \<parallel> (tr2' \<parallel> tr3')"]) 
       unfolding Inr_in_cont_par by auto
     next
       fix trB' assume "Inr trB' \<in> cont ?trB"
       then obtain tr1' tr2' tr3' where "trB' = tr1' \<parallel> (tr2' \<parallel> tr3')"
       and "Inr tr1' \<in> cont tr1" and "Inr tr2' \<in> cont tr2"
       and "Inr tr3' \<in> cont tr3" unfolding Inr_in_cont_par by auto
       thus "\<exists> trA'. Inr trA' \<in> cont ?trA \<and> ?\<phi> trA' trB'"
       apply(intro exI[of _ "(tr1' \<parallel> tr2') \<parallel> tr3'"]) 
       unfolding Inr_in_cont_par by auto
     qed
   qed
  }
  thus ?thesis by blast
qed





end