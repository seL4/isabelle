(*  Title:      HOL/HOLCF/IOA/NTP/Lemmas.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

theory Lemmas
imports Main
begin

subsubsection \<open>Logic\<close>

lemma neg_flip: "(X = (\<not> Y)) = ((\<not>X) = Y)"
  by blast


subsection \<open>Sets\<close>

lemma set_lemmas:
  "f(x) \<in> (\<Union>x. {f(x)})"
  "f x y \<in> (\<Union>x y. {f x y})"
  "\<And>a. (\<forall>x. a \<noteq> f(x)) \<Longrightarrow> a \<notin> (\<Union>x. {f(x)})"
  "\<And>a. (\<forall>x y. a \<noteq> f x y) \<Longrightarrow> a \<notin> (\<Union>x y. {f x y})"
  by auto


subsection \<open>Arithmetic\<close>

lemma pred_suc: "0<x ==> (x - 1 = y) = (x = Suc(y))"
  by (simp add: diff_Suc split: nat.split)

lemmas [simp] = hd_append set_lemmas

end
