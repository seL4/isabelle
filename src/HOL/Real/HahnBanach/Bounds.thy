(*  Title:      HOL/Real/HahnBanach/Bounds.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Bounds *}

theory Bounds = Main + Real:

text {*
  A supremum\footnote{The definition of the supremum is based on one
  in \url{http://isabelle.in.tum.de/library/HOL/HOL-Real/Lubs.html}}
  of an ordered set @{text B} w.~r.~t. @{text A} is defined as a least
  upper bound of @{text B}, which lies in @{text A}.
*}
   
text {*
  If a supremum exists, then @{text "Sup A B"} is equal to the
  supremum. *}

constdefs
  is_Sup :: "('a::order) set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  "is_Sup A B x \<equiv> isLub A B x"

  Sup :: "('a::order) set \<Rightarrow> 'a set \<Rightarrow> 'a"
  "Sup A B \<equiv> Eps (is_Sup A B)"

text {*
  The supremum of @{text B} is less than any upper bound of
  @{text B}. *}

lemma sup_le_ub: "isUb A B y \<Longrightarrow> is_Sup A B s \<Longrightarrow> s \<le> y"
  by (unfold is_Sup_def, rule isLub_le_isUb)

text {* The supremum @{text B} is an upper bound for @{text B}. *}

lemma sup_ub: "y \<in> B \<Longrightarrow> is_Sup A B s \<Longrightarrow> y \<le> s"
  by (unfold is_Sup_def, rule isLubD2)

text {*
  The supremum of a non-empty set @{text B} is greater than a lower
  bound of @{text B}. *}

lemma sup_ub1: 
  "\<forall>y \<in> B. a \<le> y \<Longrightarrow> is_Sup A B s \<Longrightarrow> x \<in> B \<Longrightarrow> a \<le> s"
proof - 
  assume "\<forall>y \<in> B. a \<le> y"  "is_Sup A B s"  "x \<in> B"
  have "a \<le> x" by (rule bspec)
  also have "x \<le> s" by (rule sup_ub)
  finally show "a \<le> s" .
qed
  
end
