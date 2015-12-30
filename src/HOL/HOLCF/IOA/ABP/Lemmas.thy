(*  Title:      HOL/HOLCF/IOA/ABP/Lemmas.thy
    Author:     Olaf Müller
*)

theory Lemmas
imports Main
begin

subsection \<open>Logic\<close>

lemma and_de_morgan_and_absorbe: "(~(A&B)) = ((~A)&B| ~B)"
  by blast

lemma bool_if_impl_or: "(if C then A else B) --> (A|B)"
  by auto

lemma exis_elim: "(? x. x=P & Q(x)) = Q(P)"
  by blast


subsection \<open>Sets\<close>

lemma set_lemmas:
    "f(x) : (UN x. {f(x)})"
    "f x y : (UN x y. {f x y})"
    "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})"
    "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"
  by auto

text \<open>2 Lemmas to add to \<open>set_lemmas\<close>, used also for action handling, 
   namely for Intersections and the empty list (compatibility of IOA!).\<close>
lemma singleton_set: "(UN b.{x. x=f(b)})= (UN b.{f(b)})"
  by blast

lemma de_morgan: "((A|B)=False) = ((~A)&(~B))"
  by blast


subsection \<open>Lists\<close>

lemma cons_not_nil: "l ~= [] --> (? x xs. l = (x#xs))"
  by (induct l) simp_all

end
