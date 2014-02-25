(*  Title:      HOL/BNF_Util.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Library for bounded natural functors.
*)

header {* Library for Bounded Natural Functors *}

theory BNF_Util
imports BNF_Cardinal_Arithmetic
begin

definition
  fun_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> bool"
where
  "fun_rel A B = (\<lambda>f g. \<forall>x y. A x y \<longrightarrow> B (f x) (g y))"

lemma fun_relI [intro]:
  assumes "\<And>x y. A x y \<Longrightarrow> B (f x) (g y)"
  shows "fun_rel A B f g"
  using assms by (simp add: fun_rel_def)

lemma fun_relD:
  assumes "fun_rel A B f g" and "A x y"
  shows "B (f x) (g y)"
  using assms by (simp add: fun_rel_def)

definition collect where
"collect F x = (\<Union>f \<in> F. f x)"

lemma fstI: "x = (y, z) \<Longrightarrow> fst x = y"
by simp

lemma sndI: "x = (y, z) \<Longrightarrow> snd x = z"
by simp

lemma bijI': "\<lbrakk>\<And>x y. (f x = f y) = (x = y); \<And>y. \<exists>x. y = f x\<rbrakk> \<Longrightarrow> bij f"
unfolding bij_def inj_on_def by auto blast

(* Operator: *)
definition "Gr A f = {(a, f a) | a. a \<in> A}"

definition "Grp A f = (\<lambda>a b. b = f a \<and> a \<in> A)"

definition vimage2p where
  "vimage2p f g R = (\<lambda>x y. R (f x) (g y))"

ML_file "Tools/BNF/bnf_util.ML"
ML_file "Tools/BNF/bnf_tactics.ML"

end
