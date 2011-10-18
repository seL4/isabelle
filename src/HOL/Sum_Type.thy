(*  Title:      HOL/Sum_Type.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*The Disjoint Sum of Two Types*}

theory Sum_Type
imports Typedef Inductive Fun
begin

subsection {* Construction of the sum type and its basic abstract operations *}

definition Inl_Rep :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool \<Rightarrow> bool" where
  "Inl_Rep a x y p \<longleftrightarrow> x = a \<and> p"

definition Inr_Rep :: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool \<Rightarrow> bool" where
  "Inr_Rep b x y p \<longleftrightarrow> y = b \<and> \<not> p"

typedef ('a, 'b) sum (infixr "+" 10) = "{f. (\<exists>a. f = Inl_Rep (a::'a)) \<or> (\<exists>b. f = Inr_Rep (b::'b))}"
  by auto

lemma Inl_RepI: "Inl_Rep a \<in> sum"
  by (auto simp add: sum_def)

lemma Inr_RepI: "Inr_Rep b \<in> sum"
  by (auto simp add: sum_def)

lemma inj_on_Abs_sum: "A \<subseteq> sum \<Longrightarrow> inj_on Abs_sum A"
  by (rule inj_on_inverseI, rule Abs_sum_inverse) auto

lemma Inl_Rep_inject: "inj_on Inl_Rep A"
proof (rule inj_onI)
  show "\<And>a c. Inl_Rep a = Inl_Rep c \<Longrightarrow> a = c"
    by (auto simp add: Inl_Rep_def fun_eq_iff)
qed

lemma Inr_Rep_inject: "inj_on Inr_Rep A"
proof (rule inj_onI)
  show "\<And>b d. Inr_Rep b = Inr_Rep d \<Longrightarrow> b = d"
    by (auto simp add: Inr_Rep_def fun_eq_iff)
qed

lemma Inl_Rep_not_Inr_Rep: "Inl_Rep a \<noteq> Inr_Rep b"
  by (auto simp add: Inl_Rep_def Inr_Rep_def fun_eq_iff)

definition Inl :: "'a \<Rightarrow> 'a + 'b" where
  "Inl = Abs_sum \<circ> Inl_Rep"

definition Inr :: "'b \<Rightarrow> 'a + 'b" where
  "Inr = Abs_sum \<circ> Inr_Rep"

lemma inj_Inl [simp]: "inj_on Inl A"
by (auto simp add: Inl_def intro!: comp_inj_on Inl_Rep_inject inj_on_Abs_sum Inl_RepI)

lemma Inl_inject: "Inl x = Inl y \<Longrightarrow> x = y"
using inj_Inl by (rule injD)

lemma inj_Inr [simp]: "inj_on Inr A"
by (auto simp add: Inr_def intro!: comp_inj_on Inr_Rep_inject inj_on_Abs_sum Inr_RepI)

lemma Inr_inject: "Inr x = Inr y \<Longrightarrow> x = y"
using inj_Inr by (rule injD)

lemma Inl_not_Inr: "Inl a \<noteq> Inr b"
proof -
  from Inl_RepI [of a] Inr_RepI [of b] have "{Inl_Rep a, Inr_Rep b} \<subseteq> sum" by auto
  with inj_on_Abs_sum have "inj_on Abs_sum {Inl_Rep a, Inr_Rep b}" .
  with Inl_Rep_not_Inr_Rep [of a b] inj_on_contraD have "Abs_sum (Inl_Rep a) \<noteq> Abs_sum (Inr_Rep b)" by auto
  then show ?thesis by (simp add: Inl_def Inr_def)
qed

lemma Inr_not_Inl: "Inr b \<noteq> Inl a" 
  using Inl_not_Inr by (rule not_sym)

lemma sumE: 
  assumes "\<And>x::'a. s = Inl x \<Longrightarrow> P"
    and "\<And>y::'b. s = Inr y \<Longrightarrow> P"
  shows P
proof (rule Abs_sum_cases [of s])
  fix f 
  assume "s = Abs_sum f" and "f \<in> sum"
  with assms show P by (auto simp add: sum_def Inl_def Inr_def)
qed

rep_datatype Inl Inr
proof -
  fix P
  fix s :: "'a + 'b"
  assume x: "\<And>x\<Colon>'a. P (Inl x)" and y: "\<And>y\<Colon>'b. P (Inr y)"
  then show "P s" by (auto intro: sumE [of s])
qed (auto dest: Inl_inject Inr_inject simp add: Inl_not_Inr)

primrec sum_map :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> 'a + 'b \<Rightarrow> 'c + 'd" where
  "sum_map f1 f2 (Inl a) = Inl (f1 a)"
| "sum_map f1 f2 (Inr a) = Inr (f2 a)"

enriched_type sum_map: sum_map proof -
  fix f g h i
  show "sum_map f g \<circ> sum_map h i = sum_map (f \<circ> h) (g \<circ> i)"
  proof
    fix s
    show "(sum_map f g \<circ> sum_map h i) s = sum_map (f \<circ> h) (g \<circ> i) s"
      by (cases s) simp_all
  qed
next
  fix s
  show "sum_map id id = id"
  proof
    fix s
    show "sum_map id id s = id s" 
      by (cases s) simp_all
  qed
qed


subsection {* Projections *}

lemma sum_case_KK [simp]: "sum_case (\<lambda>x. a) (\<lambda>x. a) = (\<lambda>x. a)"
  by (rule ext) (simp split: sum.split)

lemma surjective_sum: "sum_case (\<lambda>x::'a. f (Inl x)) (\<lambda>y::'b. f (Inr y)) = f"
proof
  fix s :: "'a + 'b"
  show "(case s of Inl (x\<Colon>'a) \<Rightarrow> f (Inl x) | Inr (y\<Colon>'b) \<Rightarrow> f (Inr y)) = f s"
    by (cases s) simp_all
qed

lemma sum_case_inject:
  assumes a: "sum_case f1 f2 = sum_case g1 g2"
  assumes r: "f1 = g1 \<Longrightarrow> f2 = g2 \<Longrightarrow> P"
  shows P
proof (rule r)
  show "f1 = g1" proof
    fix x :: 'a
    from a have "sum_case f1 f2 (Inl x) = sum_case g1 g2 (Inl x)" by simp
    then show "f1 x = g1 x" by simp
  qed
  show "f2 = g2" proof
    fix y :: 'b
    from a have "sum_case f1 f2 (Inr y) = sum_case g1 g2 (Inr y)" by simp
    then show "f2 y = g2 y" by simp
  qed
qed

lemma sum_case_weak_cong:
  "s = t \<Longrightarrow> sum_case f g s = sum_case f g t"
  -- {* Prevents simplification of @{text f} and @{text g}: much faster. *}
  by simp

primrec Projl :: "'a + 'b \<Rightarrow> 'a" where
  Projl_Inl: "Projl (Inl x) = x"

primrec Projr :: "'a + 'b \<Rightarrow> 'b" where
  Projr_Inr: "Projr (Inr x) = x"

primrec Suml :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a + 'b \<Rightarrow> 'c" where
  "Suml f (Inl x) = f x"

primrec Sumr :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a + 'b \<Rightarrow> 'c" where
  "Sumr f (Inr x) = f x"

lemma Suml_inject:
  assumes "Suml f = Suml g" shows "f = g"
proof
  fix x :: 'a
  let ?s = "Inl x \<Colon> 'a + 'b"
  from assms have "Suml f ?s = Suml g ?s" by simp
  then show "f x = g x" by simp
qed

lemma Sumr_inject:
  assumes "Sumr f = Sumr g" shows "f = g"
proof
  fix x :: 'b
  let ?s = "Inr x \<Colon> 'a + 'b"
  from assms have "Sumr f ?s = Sumr g ?s" by simp
  then show "f x = g x" by simp
qed


subsection {* The Disjoint Sum of Sets *}

definition Plus :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a + 'b) set" (infixr "<+>" 65) where
  "A <+> B = Inl ` A \<union> Inr ` B"

hide_const (open) Plus --"Valuable identifier"

lemma InlI [intro!]: "a \<in> A \<Longrightarrow> Inl a \<in> A <+> B"
by (simp add: Plus_def)

lemma InrI [intro!]: "b \<in> B \<Longrightarrow> Inr b \<in> A <+> B"
by (simp add: Plus_def)

text {* Exhaustion rule for sums, a degenerate form of induction *}

lemma PlusE [elim!]: 
  "u \<in> A <+> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> u = Inl x \<Longrightarrow> P) \<Longrightarrow> (\<And>y. y \<in> B \<Longrightarrow> u = Inr y \<Longrightarrow> P) \<Longrightarrow> P"
by (auto simp add: Plus_def)

lemma Plus_eq_empty_conv [simp]: "A <+> B = {} \<longleftrightarrow> A = {} \<and> B = {}"
by auto

lemma UNIV_Plus_UNIV [simp]: "UNIV <+> UNIV = UNIV"
proof (rule set_eqI)
  fix u :: "'a + 'b"
  show "u \<in> UNIV <+> UNIV \<longleftrightarrow> u \<in> UNIV" by (cases u) auto
qed

hide_const (open) Suml Sumr Projl Projr

hide_const (open) sum

end
