(*  Title:      HOL/Metis_Examples/Abstraction.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Example featuring Metis's support for lambda-abstractions.
*)

header {* Example Featuring Metis's Support for Lambda-Abstractions *}

theory Abstraction
imports "~~/src/HOL/Library/FuncSet"
begin

(* For Christoph Benzmüller *)
lemma "x < 1 \<and> ((op =) = (op =)) \<Longrightarrow> ((op =) = (op =)) \<and> x < (2::nat)"
by (metis nat_1_add_1 trans_less_add2)

lemma "(op = ) = (\<lambda>x y. y = x)"
by metis

consts
  monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool"
  pset  :: "'a set => 'a set"
  order :: "'a set => ('a * 'a) set"

lemma "a \<in> {x. P x} \<Longrightarrow> P a"
proof -
  assume "a \<in> {x. P x}"
  hence "a \<in> P" by (metis Collect_def)
  thus "P a" by (metis mem_def)
qed

lemma Collect_triv: "a \<in> {x. P x} \<Longrightarrow> P a"
by (metis mem_Collect_eq)

lemma "a \<in> {x. P x --> Q x} \<Longrightarrow> a \<in> {x. P x} \<Longrightarrow> a \<in> {x. Q x}"
by (metis Collect_imp_eq ComplD UnE)

lemma "(a, b) \<in> Sigma A B \<Longrightarrow> a \<in> A & b \<in> B a"
proof -
  assume A1: "(a, b) \<in> Sigma A B"
  hence F1: "b \<in> B a" by (metis mem_Sigma_iff)
  have F2: "a \<in> A" by (metis A1 mem_Sigma_iff)
  have "b \<in> B a" by (metis F1)
  thus "a \<in> A \<and> b \<in> B a" by (metis F2)
qed

lemma Sigma_triv: "(a, b) \<in> Sigma A B \<Longrightarrow> a \<in> A & b \<in> B a"
by (metis SigmaD1 SigmaD2)

lemma "(a, b) \<in> (SIGMA x:A. {y. x = f y}) \<Longrightarrow> a \<in> A \<and> a = f b"
by (metis (full_types, lam_lifting) CollectD SigmaD1 SigmaD2)

lemma "(a, b) \<in> (SIGMA x:A. {y. x = f y}) \<Longrightarrow> a \<in> A \<and> a = f b"
proof -
  assume A1: "(a, b) \<in> (SIGMA x:A. {y. x = f y})"
  hence F1: "a \<in> A" by (metis mem_Sigma_iff)
  have "b \<in> {R. a = f R}" by (metis A1 mem_Sigma_iff)
  hence F2: "b \<in> (\<lambda>R. a = f R)" by (metis Collect_def)
  hence "a = f b" by (unfold mem_def)
  thus "a \<in> A \<and> a = f b" by (metis F1)
qed

lemma "(cl, f) \<in> CLF \<Longrightarrow> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) \<Longrightarrow> f \<in> pset cl"
by (metis Collect_mem_eq SigmaD2)

lemma "(cl, f) \<in> CLF \<Longrightarrow> CLF = (SIGMA cl: CL.{f. f \<in> pset cl}) \<Longrightarrow> f \<in> pset cl"
proof -
  assume A1: "(cl, f) \<in> CLF"
  assume A2: "CLF = (SIGMA cl:CL. {f. f \<in> pset cl})"
  have F1: "\<forall>v. (\<lambda>R. R \<in> v) = v" by (metis Collect_mem_eq Collect_def)
  have "\<forall>v u. (u, v) \<in> CLF \<longrightarrow> v \<in> {R. R \<in> pset u}" by (metis A2 mem_Sigma_iff)
  hence "\<forall>v u. (u, v) \<in> CLF \<longrightarrow> v \<in> pset u" by (metis F1 Collect_def)
  thus "f \<in> pset cl" by (metis A1)
qed

lemma
  "(cl, f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) \<Longrightarrow>
   f \<in> pset cl \<rightarrow> pset cl"
by (metis (no_types) Collect_def Sigma_triv mem_def)

lemma
  "(cl, f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) \<Longrightarrow>
   f \<in> pset cl \<rightarrow> pset cl"
proof -
  assume A1: "(cl, f) \<in> (SIGMA cl:CL. {f. f \<in> pset cl \<rightarrow> pset cl})"
  have F1: "\<forall>v. (\<lambda>R. R \<in> v) = v" by (metis Collect_mem_eq Collect_def)
  have "f \<in> {R. R \<in> pset cl \<rightarrow> pset cl}" using A1 by simp
  thus "f \<in> pset cl \<rightarrow> pset cl" by (metis F1 Collect_def)
qed

lemma
  "(cl, f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) \<Longrightarrow>
   f \<in> pset cl \<inter> cl"
by (metis (no_types) Collect_conj_eq Int_def Sigma_triv inf_idem)

lemma
  "(cl, f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) \<Longrightarrow>
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

lemma
  "(cl, f) \<in> (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) \<Longrightarrow>
   (f \<in> pset cl \<rightarrow> pset cl)  &  (monotone f (pset cl) (order cl))"
by auto

lemma
  "(cl, f) \<in> CLF \<Longrightarrow>
   CLF \<subseteq> (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) \<Longrightarrow>
   f \<in> pset cl \<inter> cl"
by (metis (lam_lifting) Collect_def Sigma_triv mem_def subsetD)

lemma
  "(cl, f) \<in> CLF \<Longrightarrow>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<inter> cl}) \<Longrightarrow>
   f \<in> pset cl \<inter> cl"
by (metis (lam_lifting) Int_Collect SigmaD2 inf1I mem_def)

lemma
  "(cl, f) \<in> CLF \<Longrightarrow>
   CLF \<subseteq> (SIGMA cl': CL. {f. f \<in> pset cl' \<rightarrow> pset cl'}) \<Longrightarrow>
   f \<in> pset cl \<rightarrow> pset cl"
by (metis (lam_lifting) Collect_def Sigma_triv mem_def subsetD)

lemma
  "(cl, f) \<in> CLF \<Longrightarrow>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl}) \<Longrightarrow>
   f \<in> pset cl \<rightarrow> pset cl"
by (metis (lam_lifting) Collect_def Sigma_triv mem_def)

lemma
  "(cl, f) \<in> CLF \<Longrightarrow>
   CLF = (SIGMA cl: CL. {f. f \<in> pset cl \<rightarrow> pset cl & monotone f (pset cl) (order cl)}) \<Longrightarrow>
   (f \<in> pset cl \<rightarrow> pset cl) & (monotone f (pset cl) (order cl))"
by auto

lemma "map (\<lambda>x. (f x, g x)) xs = zip (map f xs) (map g xs)"
apply (induct xs)
 apply (metis map.simps(1) zip_Nil)
by auto

lemma
  "map (\<lambda>w. (w -> w, w \<times> w)) xs =
   zip (map (\<lambda>w. w -> w) xs) (map (\<lambda>w. w \<times> w) xs)"
apply (induct xs)
 apply (metis map.simps(1) zip_Nil)
by auto

lemma "(\<lambda>x. Suc (f x)) ` {x. even x} \<subseteq> A \<Longrightarrow> \<forall>x. even x --> Suc (f x) \<in> A"
by (metis Collect_def image_eqI mem_def subsetD)

lemma
  "(\<lambda>x. f (f x)) ` ((\<lambda>x. Suc(f x)) ` {x. even x}) \<subseteq> A \<Longrightarrow>
   (\<forall>x. even x --> f (f (Suc(f x))) \<in> A)"
by (metis Collect_def imageI mem_def set_rev_mp)

lemma "f \<in> (\<lambda>u v. b \<times> u \<times> v) ` A \<Longrightarrow> \<forall>u v. P (b \<times> u \<times> v) \<Longrightarrow> P(f y)"
by (metis (lam_lifting) imageE)

lemma image_TimesA: "(\<lambda>(x, y). (f x, g y)) ` (A \<times> B) = (f ` A) \<times> (g ` B)"
by (metis map_pair_def map_pair_surj_on)

lemma image_TimesB:
    "(\<lambda>(x, y, z). (f x, g y, h z)) ` (A \<times> B \<times> C) = (f ` A) \<times> (g ` B) \<times> (h ` C)"
by force

lemma image_TimesC:
  "(\<lambda>(x, y). (x \<rightarrow> x, y \<times> y)) ` (A \<times> B) =
   ((\<lambda>x. x \<rightarrow> x) ` A) \<times> ((\<lambda>y. y \<times> y) ` B)"
by (metis image_TimesA)

end
