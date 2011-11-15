(*  Title:      HOL/Metis_Examples/Abstraction.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Example featuring Metis's support for lambda-abstractions.
*)

header {* Example Featuring Metis's Support for Lambda-Abstractions *}

theory Abstraction
imports Main "~~/src/HOL/Library/FuncSet"
begin

declare [[metis_new_skolemizer]]

(*For Christoph Benzmueller*)
lemma "x<1 & ((op=) = (op=)) ==> ((op=) = (op=)) & (x<(2::nat))"
  by (metis One_nat_def less_Suc0 not_less0 not_less_eq numeral_2_eq_2)

(*this is a theorem, but we can't prove it unless ext is applied explicitly
lemma "(op=) = (%x y. y=x)"
*)

consts
  monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool"
  pset  :: "'a set => 'a set"
  order :: "'a set => ('a * 'a) set"

declare [[ sledgehammer_problem_prefix = "Abstraction__Collect_triv" ]]
lemma (*Collect_triv:*) "a \<in> {x. P x} ==> P a"
proof -
  assume "a \<in> {x. P x}"
  hence "a \<in> P" by (metis Collect_def)
  hence "P a" by (metis mem_def)
  thus "P a" by metis
qed

lemma Collect_triv: "a \<in> {x. P x} ==> P a"
by (metis mem_Collect_eq)


declare [[ sledgehammer_problem_prefix = "Abstraction__Collect_mp" ]]
lemma "a \<in> {x. P x --> Q x} ==> a \<in> {x. P x} ==> a \<in> {x. Q x}"
  by (metis Collect_imp_eq ComplD UnE)

declare [[ sledgehammer_problem_prefix = "Abstraction__Sigma_triv" ]]
lemma "(a,b) \<in> Sigma A B ==> a \<in> A & b \<in> B a"
proof -
  assume A1: "(a, b) \<in> Sigma A B"
  hence F1: "b \<in> B a" by (metis mem_Sigma_iff)
  have F2: "a \<in> A" by (metis A1 mem_Sigma_iff)
  have "b \<in> B a" by (metis F1)
  thus "a \<in> A \<and> b \<in> B a" by (metis F2)
qed

lemma Sigma_triv: "(a,b) \<in> Sigma A B ==> a \<in> A & b \<in> B a"
by (metis SigmaD1 SigmaD2)

declare [[ sledgehammer_problem_prefix = "Abstraction__Sigma_Collect" ]]
lemma "(a, b) \<in> (SIGMA x:A. {y. x = f y}) \<Longrightarrow> a \<in> A \<and> a = f b"
(* Metis says this is satisfiable!
by (metis CollectD SigmaD1 SigmaD2)
*)
by (meson CollectD SigmaD1 SigmaD2)


lemma "(a, b) \<in> (SIGMA x:A. {y. x = f y}) \<Longrightarrow> a \<in> A \<and> a = f b"
by (metis mem_Sigma_iff singleton_conv2 vimage_Collect_eq vimage_singleton_eq)

lemma "(a, b) \<in> (SIGMA x:A. {y. x = f y}) \<Longrightarrow> a \<in> A \<and> a = f b"
proof -
  assume A1: "(a, b) \<in> (SIGMA x:A. {y. x = f y})"
  hence F1: "a \<in> A" by (metis mem_Sigma_iff)
  have "b \<in> {R. a = f R}" by (metis A1 mem_Sigma_iff)
  hence F2: "b \<in> (\<lambda>R. a = f R)" by (metis Collect_def)
  hence "a = f b" by (unfold mem_def)
  thus "a \<in> A \<and> a = f b" by (metis F1)
qed


declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_eq_in_pp" ]]
lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"
by (metis Collect_mem_eq SigmaD2)

lemma "(cl,f) \<in> CLF ==> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) ==> f \<in> pset cl"
proof -
  assume A1: "(cl, f) \<in> CLF"
  assume A2: "CLF = (SIGMA cl:CL. {f. f \<in> pset cl})"
  have F1: "\<forall>v. (\<lambda>R. R \<in> v) = v" by (metis Collect_mem_eq Collect_def)
  have "\<forall>v u. (u, v) \<in> CLF \<longrightarrow> v \<in> {R. R \<in> pset u}" by (metis A2 mem_Sigma_iff)
  hence "\<forall>v u. (u, v) \<in> CLF \<longrightarrow> v \<in> pset u" by (metis F1 Collect_def)
  hence "f \<in> pset cl" by (metis A1)
  thus "f \<in> pset cl" by metis
qed

declare [[ sledgehammer_problem_prefix = "Abstraction__Sigma_Collect_Pi" ]]
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==>
    f \<in> pset cl \<rightarrow> pset cl"
proof -
  assume A1: "(cl, f) \<in> (SIGMA cl:CL. {f. f \<in> pset cl \<rightarrow> pset cl})"
  have F1: "\<forall>v. (\<lambda>R. R \<in> v) = v" by (metis Collect_mem_eq Collect_def)
  have "f \<in> {R. R \<in> pset cl \<rightarrow> pset cl}" using A1 by simp
  hence "f \<in> pset cl \<rightarrow> pset cl" by (metis F1 Collect_def)
  thus "f \<in> pset cl \<rightarrow> pset cl" by metis
qed

declare [[ sledgehammer_problem_prefix = "Abstraction__Sigma_Collect_Int" ]]
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
proof -
  assume A1: "(cl, f) \<in> (SIGMA cl:CL. {f. f \<in> pset cl \<inter> cl})"
  have F1: "\<forall>v. (\<lambda>R. R \<in> v) = v" by (metis Collect_mem_eq Collect_def)
  have "f \<in> {R. R \<in> pset cl \<inter> cl}" using A1 by simp
  hence "f \<in> Id_on cl `` pset cl" by (metis F1 Int_commute Image_Id_on Collect_def)
  hence "f \<in> Id_on cl `` pset cl" by metis
  hence "f \<in> cl \<inter> pset cl" by (metis Image_Id_on)
  thus "f \<in> pset cl \<inter> cl" by (metis Int_commute)
qed


declare [[ sledgehammer_problem_prefix = "Abstraction__Sigma_Collect_Pi_mono" ]]
lemma
    "(cl,f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_subset_Collect_Int" ]]
lemma "(cl,f) \<in> CLF ==>
   CLF \<subseteq> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by auto


declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_eq_Collect_Int" ]]
lemma "(cl,f) \<in> CLF ==>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) ==>
   f \<in> pset cl \<inter> cl"
by auto


declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_subset_Collect_Pi" ]]
lemma
   "(cl,f) \<in> CLF ==>
    CLF \<subseteq> (SIGMA cl': CL. {f. f \<in> pset cl' \<rightarrow> pset cl'}) ==>
    f \<in> pset cl \<rightarrow> pset cl"
by fast


declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_eq_Collect_Pi" ]]
lemma
  "(cl,f) \<in> CLF ==>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) ==>
   f \<in> pset cl \<rightarrow> pset cl"
by auto


declare [[ sledgehammer_problem_prefix = "Abstraction__CLF_eq_Collect_Pi_mono" ]]
lemma
  "(cl,f) \<in> CLF ==>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) ==>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

declare [[ sledgehammer_problem_prefix = "Abstraction__map_eq_zipA" ]]
lemma "map (%x. (f x, g x)) xs = zip (map f xs) (map g xs)"
apply (induct xs)
 apply (metis map_is_Nil_conv zip.simps(1))
by auto

declare [[ sledgehammer_problem_prefix = "Abstraction__map_eq_zipB" ]]
lemma "map (%w. (w -> w, w \<times> w)) xs =
       zip (map (%w. w -> w) xs) (map (%w. w \<times> w) xs)"
apply (induct xs)
 apply (metis Nil_is_map_conv zip_Nil)
by auto

declare [[ sledgehammer_problem_prefix = "Abstraction__image_evenA" ]]
lemma "(%x. Suc(f x)) ` {x. even x} <= A ==> (\<forall>x. even x --> Suc(f x) \<in> A)"
by (metis Collect_def image_subset_iff mem_def)

declare [[ sledgehammer_problem_prefix = "Abstraction__image_evenB" ]]
lemma "(%x. f (f x)) ` ((%x. Suc(f x)) ` {x. even x}) <= A
       ==> (\<forall>x. even x --> f (f (Suc(f x))) \<in> A)"
by (metis Collect_def imageI image_image image_subset_iff mem_def)

declare [[ sledgehammer_problem_prefix = "Abstraction__image_curry" ]]
lemma "f \<in> (%u v. b \<times> u \<times> v) ` A ==> \<forall>u v. P (b \<times> u \<times> v) ==> P(f y)"
(*sledgehammer*)
by auto

declare [[ sledgehammer_problem_prefix = "Abstraction__image_TimesA" ]]
lemma image_TimesA: "(%(x,y). (f x, g y)) ` (A \<times> B) = (f`A) \<times> (g`B)"
(*sledgehammer*)
apply (rule equalityI)
(***Even the two inclusions are far too difficult
using [[ sledgehammer_problem_prefix = "Abstraction__image_TimesA_simpler"]]
***)
apply (rule subsetI)
apply (erule imageE)
(*V manages from here with help: Abstraction__image_TimesA_simpler_1_b.p*)
apply (erule ssubst)
apply (erule SigmaE)
(*V manages from here: Abstraction__image_TimesA_simpler_1_a.p*)
apply (erule ssubst)
apply (subst split_conv)
apply (rule SigmaI)
apply (erule imageI) +
txt{*subgoal 2*}
apply (clarify )
apply (simp add: )
apply (rule rev_image_eqI)
apply (blast intro: elim:)
apply (simp add: )
done

(*Given the difficulty of the previous problem, these two are probably
impossible*)

declare [[ sledgehammer_problem_prefix = "Abstraction__image_TimesB" ]]
lemma image_TimesB:
    "(%(x,y,z). (f x, g y, h z)) ` (A \<times> B \<times> C) = (f`A) \<times> (g`B) \<times> (h`C)"
(*sledgehammer*)
by force

declare [[ sledgehammer_problem_prefix = "Abstraction__image_TimesC" ]]
lemma image_TimesC:
    "(%(x,y). (x \<rightarrow> x, y \<times> y)) ` (A \<times> B) =
     ((%x. x \<rightarrow> x) ` A) \<times> ((%y. y \<times> y) ` B)"
(*sledgehammer*)
by auto

end
