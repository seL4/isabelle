(*  Title:      FOL/ex/Quantifiers_Cla.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>First-Order Logic: quantifier examples (classical version)\<close>

theory Quantifiers_Cla
imports FOL
begin

lemma \<open>(\<forall>x y. P(x,y)) \<longrightarrow> (\<forall>y x. P(x,y))\<close>
  by fast

lemma \<open>(\<exists>x y. P(x,y)) \<longrightarrow> (\<exists>y x. P(x,y))\<close>
  by fast


text \<open>Converse is false.\<close>
lemma \<open>(\<forall>x. P(x)) \<or> (\<forall>x. Q(x)) \<longrightarrow> (\<forall>x. P(x) \<or> Q(x))\<close>
  by fast

lemma \<open>(\<forall>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q(x)))\<close>
  by fast


lemma \<open>(\<forall>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x. P(x)) \<longrightarrow> Q)\<close>
  by fast


text \<open>Some harder ones.\<close>

lemma \<open>(\<exists>x. P(x) \<or> Q(x)) \<longleftrightarrow> (\<exists>x. P(x)) \<or> (\<exists>x. Q(x))\<close>
  by fast

\<comment> \<open>Converse is false.\<close>
lemma \<open>(\<exists>x. P(x) \<and> Q(x)) \<longrightarrow> (\<exists>x. P(x)) \<and> (\<exists>x. Q(x))\<close>
  by fast


text \<open>Basic test of quantifier reasoning.\<close>

\<comment> \<open>TRUE\<close>
lemma \<open>(\<exists>y. \<forall>x. Q(x,y)) \<longrightarrow> (\<forall>x. \<exists>y. Q(x,y))\<close>
  by fast

lemma \<open>(\<forall>x. Q(x)) \<longrightarrow> (\<exists>x. Q(x))\<close>
  by fast


text \<open>The following should fail, as they are false!\<close>

lemma \<open>(\<forall>x. \<exists>y. Q(x,y)) \<longrightarrow> (\<exists>y. \<forall>x. Q(x,y))\<close>
  apply fast?
  oops

lemma \<open>(\<exists>x. Q(x)) \<longrightarrow> (\<forall>x. Q(x))\<close>
  apply fast?
  oops

schematic_goal \<open>P(?a) \<longrightarrow> (\<forall>x. P(x))\<close>
  apply fast?
  oops

schematic_goal \<open>(P(?a) \<longrightarrow> (\<forall>x. Q(x))) \<longrightarrow> (\<forall>x. P(x) \<longrightarrow> Q(x))\<close>
  apply fast?
  oops


text \<open>Back to things that are provable \dots\<close>

lemma \<open>(\<forall>x. P(x) \<longrightarrow> Q(x)) \<and> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))\<close>
  by fast

text \<open>An example of why \<open>exI\<close> should be delayed as long as possible.\<close>
lemma \<open>(P \<longrightarrow> (\<exists>x. Q(x))) \<and> P \<longrightarrow> (\<exists>x. Q(x))\<close>
  by fast

schematic_goal \<open>(\<forall>x. P(x) \<longrightarrow> Q(f(x))) \<and> (\<forall>x. Q(x) \<longrightarrow> R(g(x))) \<and> P(d) \<longrightarrow> R(?a)\<close>
  by fast

lemma \<open>(\<forall>x. Q(x)) \<longrightarrow> (\<exists>x. Q(x))\<close>
  by fast


text \<open>Some slow ones\<close>

text \<open>Principia Mathematica *11.53\<close>
lemma \<open>(\<forall>x y. P(x) \<longrightarrow> Q(y)) \<longleftrightarrow> ((\<exists>x. P(x)) \<longrightarrow> (\<forall>y. Q(y)))\<close>
  by fast

(*Principia Mathematica *11.55  *)
lemma \<open>(\<exists>x y. P(x) \<and> Q(x,y)) \<longleftrightarrow> (\<exists>x. P(x) \<and> (\<exists>y. Q(x,y)))\<close>
  by fast

(*Principia Mathematica *11.61  *)
lemma \<open>(\<exists>y. \<forall>x. P(x) \<longrightarrow> Q(x,y)) \<longrightarrow> (\<forall>x. P(x) \<longrightarrow> (\<exists>y. Q(x,y)))\<close>
  by fast

end
