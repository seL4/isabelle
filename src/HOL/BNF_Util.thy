(*  Title:      HOL/BNF_Util.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Library for bounded natural functors.
*)

header {* Library for Bounded Natural Functors *}

theory BNF_Util
imports BNF_Cardinal_Arithmetic
  Transfer (*FIXME: define fun_rel here, reuse in Transfer once this theory is in HOL*)
begin

definition collect where
"collect F x = (\<Union>f \<in> F. f x)"

lemma fstI: "x = (y, z) \<Longrightarrow> fst x = y"
by simp

lemma sndI: "x = (y, z) \<Longrightarrow> snd x = z"
by simp

lemma bijI: "\<lbrakk>\<And>x y. (f x = f y) = (x = y); \<And>y. \<exists>x. y = f x\<rbrakk> \<Longrightarrow> bij f"
unfolding bij_def inj_on_def by auto blast

(* Operator: *)
definition "Gr A f = {(a, f a) | a. a \<in> A}"

definition "Grp A f = (\<lambda>a b. b = f a \<and> a \<in> A)"

ML_file "Tools/BNF/bnf_util.ML"
ML_file "Tools/BNF/bnf_tactics.ML"

end
