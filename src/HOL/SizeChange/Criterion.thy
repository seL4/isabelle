(*  Title:      HOL/Library/SCT_Definition.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* The Size-Change Principle (Definition) *}

theory Criterion
imports Graphs Infinite_Set
begin

subsection {* Size-Change Graphs *}

datatype sedge =
    LESS ("\<down>")
  | LEQ ("\<Down>")

instantiation sedge :: comm_monoid_mult
begin

definition
  one_sedge_def: "1 = \<Down>"

definition
  mult_sedge_def:" a * b = (if a = \<down> then \<down> else b)"

instance  proof
  fix a b c :: sedge
  show "a * b * c = a * (b * c)" by (simp add:mult_sedge_def)
  show "1 * a = a" by (simp add:mult_sedge_def one_sedge_def)
  show "a * b = b * a" unfolding mult_sedge_def
    by (cases a, simp) (cases b, auto)
qed

end

lemma sedge_UNIV:
  "UNIV = { LESS, LEQ }"
proof (intro equalityI subsetI)
  fix x show "x \<in> { LESS, LEQ }"
    by (cases x) auto
qed auto

instance sedge :: finite
proof
  show "finite (UNIV::sedge set)"
    by (simp add: sedge_UNIV)
qed

lemmas [code func] = sedge_UNIV


types 'a scg = "('a, sedge) graph"
types 'a acg = "('a, 'a scg) graph"


subsection {* Size-Change Termination *}

abbreviation (input)
  "desc P Q == ((\<exists>n.\<forall>i\<ge>n. P i) \<and> (\<exists>\<^sub>\<infinity>i. Q i))"

abbreviation (input)
  "dsc G i j \<equiv> has_edge G i LESS j"

abbreviation (input)
  "eq G i j \<equiv> has_edge G i LEQ j"

abbreviation
  eql :: "'a scg \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
("_ \<turnstile> _ \<leadsto> _")
where
  "eql G i j \<equiv> has_edge G i LESS j \<or> has_edge G i LEQ j"


abbreviation (input) descat :: "('a, 'a scg) ipath \<Rightarrow> 'a sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "descat p \<theta> i \<equiv> has_edge (snd (p i)) (\<theta> i) LESS (\<theta> (Suc i))"

abbreviation (input) eqat :: "('a, 'a scg) ipath \<Rightarrow> 'a sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "eqat p \<theta> i \<equiv> has_edge (snd (p i)) (\<theta> i) LEQ (\<theta> (Suc i))"


abbreviation (input) eqlat :: "('a, 'a scg) ipath \<Rightarrow> 'a sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "eqlat p \<theta> i \<equiv> (has_edge (snd (p i)) (\<theta> i) LESS (\<theta> (Suc i))
                  \<or> has_edge (snd (p i)) (\<theta> i) LEQ (\<theta> (Suc i)))"


definition is_desc_thread :: "'a sequence \<Rightarrow> ('a, 'a scg) ipath \<Rightarrow> bool"
where
  "is_desc_thread \<theta> p = ((\<exists>n.\<forall>i\<ge>n. eqlat p \<theta> i) \<and> (\<exists>\<^sub>\<infinity>i. descat p \<theta> i))" 

definition SCT :: "'a acg \<Rightarrow> bool"
where
  "SCT \<A> = 
  (\<forall>p. has_ipath \<A> p \<longrightarrow> (\<exists>\<theta>. is_desc_thread \<theta> p))"



definition no_bad_graphs :: "'a acg \<Rightarrow> bool"
where
  "no_bad_graphs A = 
  (\<forall>n G. has_edge A n G n \<and> G * G = G
  \<longrightarrow> (\<exists>p. has_edge G p LESS p))"


definition SCT' :: "'a acg \<Rightarrow> bool"
where
  "SCT' A = no_bad_graphs (tcl A)"

end
