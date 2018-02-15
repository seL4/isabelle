(*  Title:      HOL/HOLCF/IOA/ABP/Lemmas.thy
    Author:     Olaf Müller
*)

theory Lemmas
imports Main
begin

subsection \<open>Logic\<close>

lemma and_de_morgan_and_absorbe: "(\<not>(A\<and>B)) = ((\<not>A)\<and>B\<or> \<not>B)"
  by blast

lemma bool_if_impl_or: "(if C then A else B) \<longrightarrow> (A\<or>B)"
  by auto

lemma exis_elim: "(\<exists>x. x=P \<and> Q(x)) = Q(P)"
  by blast


subsection \<open>Sets\<close>

lemma set_lemmas:
    "f(x) \<in> (\<Union>x. {f(x)})"
    "f x y \<in> (\<Union>x y. {f x y})"
    "\<And>a. (\<forall>x. a \<noteq> f(x)) \<Longrightarrow> a \<notin> (\<Union>x. {f(x)})"
    "\<And>a. (\<forall>x y. a \<noteq> f x y) ==> a \<notin> (\<Union>x y. {f x y})"
  by auto

text \<open>2 Lemmas to add to \<open>set_lemmas\<close>, used also for action handling, 
   namely for Intersections and the empty list (compatibility of IOA!).\<close>
lemma singleton_set: "(\<Union>b.{x. x=f(b)}) = (\<Union>b.{f(b)})"
  by blast

lemma de_morgan: "((A\<or>B)=False) = ((\<not>A)\<and>(\<not>B))"
  by blast


subsection \<open>Lists\<close>

lemma cons_not_nil: "l \<noteq> [] \<longrightarrow> (\<exists>x xs. l = (x#xs))"
  by (induct l) simp_all

end
