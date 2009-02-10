(*  Title:      HOL/ex/Induction_Scheme.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Examples of automatically derived induction rules *}

theory Induction_Scheme
imports Main
begin

subsection {* Some simple induction principles on nat *}

lemma nat_standard_induct: (* cf. Nat.thy *)
  "\<lbrakk>P 0; \<And>n. P n \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P x"
by induct_scheme (pat_completeness, lexicographic_order)

lemma nat_induct2:
  "\<lbrakk> P 0; P (Suc 0); \<And>k. P k ==> P (Suc k) ==> P (Suc (Suc k)) \<rbrakk>
  \<Longrightarrow> P n"
by induct_scheme (pat_completeness, lexicographic_order)

lemma minus_one_induct:
  "\<lbrakk>\<And>n::nat. (n \<noteq> 0 \<Longrightarrow> P (n - 1)) \<Longrightarrow> P n\<rbrakk> \<Longrightarrow> P x"
by induct_scheme (pat_completeness, lexicographic_order)

theorem diff_induct: (* cf. Nat.thy *)
  "(!!x. P x 0) ==> (!!y. P 0 (Suc y)) ==>
    (!!x y. P x y ==> P (Suc x) (Suc y)) ==> P m n"
by induct_scheme (pat_completeness, lexicographic_order)

lemma list_induct2': (* cf. List.thy *)
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
by induct_scheme (pat_completeness, lexicographic_order)

theorem even_odd_induct:
  assumes "R 0"
  assumes "Q 0"
  assumes "\<And>n. Q n \<Longrightarrow> R (Suc n)"
  assumes "\<And>n. R n \<Longrightarrow> Q (Suc n)"
  shows "R n" "Q n"
  using assms
by induct_scheme (pat_completeness+, lexicographic_order)

end