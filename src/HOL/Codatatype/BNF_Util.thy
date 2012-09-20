(*  Title:      HOL/Codatatype/BNF_Util.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Library for bounded natural functors.
*)

header {* Library for Bounded Natural Functors *}

theory BNF_Util
imports "../Cardinals/Cardinal_Arithmetic"
begin

lemma subset_Collect_iff: "B \<subseteq> A \<Longrightarrow> (B \<subseteq> {x \<in> A. P x}) = (\<forall>x \<in> B. P x)"
by blast

lemma subset_CollectI: "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> Q x \<Longrightarrow> P x) \<Longrightarrow> ({x \<in> B. Q x} \<subseteq> {x \<in> A. P x})"
by blast

definition collect where
"collect F x = (\<Union>f \<in> F. f x)"

(* Weak pullbacks: *)
definition wpull where
"wpull A B1 B2 f1 f2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow> (\<exists> a \<in> A. p1 a = b1 \<and> p2 a = b2))"

(* Weak pseudo-pullbacks *)
definition wppull where
"wppull A B1 B2 f1 f2 e1 e2 p1 p2 \<longleftrightarrow>
 (\<forall> b1 b2. b1 \<in> B1 \<and> b2 \<in> B2 \<and> f1 b1 = f2 b2 \<longrightarrow>
           (\<exists> a \<in> A. e1 (p1 a) = e1 b1 \<and> e2 (p2 a) = e2 b2))"

lemma fst_snd: "\<lbrakk>snd x = (y, z)\<rbrakk> \<Longrightarrow> fst (snd x) = y"
by simp

lemma snd_snd: "\<lbrakk>snd x = (y, z)\<rbrakk> \<Longrightarrow> snd (snd x) = z"
by simp

lemma fstI: "x = (y, z) \<Longrightarrow> fst x = y"
by simp

lemma sndI: "x = (y, z) \<Longrightarrow> snd x = z"
by simp

lemma bijI: "\<lbrakk>\<And>x y. (f x = f y) = (x = y); \<And>y. \<exists>x. y = f x\<rbrakk> \<Longrightarrow> bij f"
unfolding bij_def inj_on_def by auto blast

lemma pair_mem_Collect_split:
"(\<lambda>x y. (x, y) \<in> {(x, y). P x y}) = P"
by simp

lemma Collect_pair_mem_eq: "{(x, y). (x, y) \<in> R} = R"
by simp

lemma Collect_fst_snd_mem_eq: "{p. (fst p, snd p) \<in> A} = A"
by simp

(* Operator: *)
definition "Gr A f = {(a, f a) | a. a \<in> A}"

ML_file "Tools/bnf_util.ML"
ML_file "Tools/bnf_tactics.ML"

end
