(*  Title:      HOLCF/IOA/ABP/Lemmas.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

theory Lemmas
imports Main
begin

subsection {* Logic *}

lemma and_de_morgan_and_absorbe: "(~(A&B)) = ((~A)&B| ~B)"
  by blast

lemma bool_if_impl_or: "(if C then A else B) --> (A|B)"
  by auto

lemma exis_elim: "(? x. x=P & Q(x)) = Q(P)"
  by blast


subsection {* Sets *}

lemma set_lemmas:
    "f(x) : (UN x. {f(x)})"
    "f x y : (UN x y. {f x y})"
    "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})"
    "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"
  by auto

text {* 2 Lemmas to add to @{text "set_lemmas"}, used also for action handling, 
   namely for Intersections and the empty list (compatibility of IOA!). *}
lemma singleton_set: "(UN b.{x. x=f(b)})= (UN b.{f(b)})"
  by blast

lemma de_morgan: "((A|B)=False) = ((~A)&(~B))"
  by blast


subsection {* Lists *}

lemma hd_append: "hd(l@m) = (if l~=[] then hd(l) else hd(m))"
  by (induct l) simp_all

lemma cons_not_nil: "l ~= [] --> (? x xs. l = (x#xs))"
  by (induct l) simp_all

end
