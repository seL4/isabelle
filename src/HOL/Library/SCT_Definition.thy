(*  Title:      HOL/Library/SCT_Definition.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header ""

theory SCT_Definition
imports Graphs Infinite_Set
begin

subsection {* Size-Change Graphs *}

datatype sedge =
    LESS ("\<down>")
  | LEQ ("\<Down>")

instance sedge :: times ..
instance sedge :: one ..

defs (overloaded)
  one_sedge_def: "1 == \<Down>"
  mult_sedge_def:" a * b == (if a = \<down> then \<down> else b)"

instance sedge :: comm_monoid_mult
proof
  fix a b c :: sedge
  show "a * b * c = a * (b * c)" by (simp add:mult_sedge_def)
  show "1 * a = a" by (simp add:mult_sedge_def one_sedge_def)
  show "a * b = b * a" unfolding mult_sedge_def
    by (cases a, simp) (cases b, auto)
qed

instance sedge :: finite
proof
  have a: "UNIV = { LESS, LEQ }"
    by auto (case_tac x, auto) (* FIXME *)
  show "finite (UNIV::sedge set)"
    by (simp add:a)
qed


types scg = "(nat, sedge) graph"
types acg = "(nat, scg) graph"


subsection {* Size-Change Termination *}

abbreviation (input)
  "desc P Q == ((\<exists>n.\<forall>i\<ge>n. P i) \<and> (\<exists>\<^sub>\<infinity>i. Q i))"

abbreviation (input)
  "dsc G i j \<equiv> has_edge G i LESS j"

abbreviation (input)
  "eq G i j \<equiv> has_edge G i LEQ j"

abbreviation
  eql :: "scg \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
("_ \<turnstile> _ \<leadsto> _")
where
  "eql G i j \<equiv> has_edge G i LESS j \<or> has_edge G i LEQ j"


abbreviation (input) descat :: "(nat, scg) ipath \<Rightarrow> nat sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "descat p \<theta> i \<equiv> has_edge (snd (p i)) (\<theta> i) LESS (\<theta> (Suc i))"

abbreviation (input) eqat :: "(nat, scg) ipath \<Rightarrow> nat sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "eqat p \<theta> i \<equiv> has_edge (snd (p i)) (\<theta> i) LEQ (\<theta> (Suc i))"


abbreviation eqlat :: "(nat, scg) ipath \<Rightarrow> nat sequence \<Rightarrow> nat \<Rightarrow> bool"
where
  "eqlat p \<theta> i \<equiv> (has_edge (snd (p i)) (\<theta> i) LESS (\<theta> (Suc i))
                  \<or> has_edge (snd (p i)) (\<theta> i) LEQ (\<theta> (Suc i)))"


definition is_desc_thread :: "nat sequence \<Rightarrow> (nat, scg) ipath \<Rightarrow> bool"
where
  "is_desc_thread \<theta> p = ((\<exists>n.\<forall>i\<ge>n. eqlat p \<theta> i) \<and> (\<exists>\<^sub>\<infinity>i. descat p \<theta> i))" 

definition SCT :: "acg \<Rightarrow> bool"
where
  "SCT \<A> = 
  (\<forall>p. has_ipath \<A> p \<longrightarrow> (\<exists>\<theta>. is_desc_thread \<theta> p))"



definition no_bad_graphs :: "acg \<Rightarrow> bool"
where
  "no_bad_graphs A = 
  (\<forall>n G. has_edge A n G n \<and> G * G = G
  \<longrightarrow> (\<exists>p. has_edge G p LESS p))"


definition SCT' :: "acg \<Rightarrow> bool"
where
  "SCT' A = no_bad_graphs (tcl A)"

end
