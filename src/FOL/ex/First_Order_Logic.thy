(*  Title:      FOL/ex/First_Order_Logic.thy
    Author:     Markus Wenzel, TU Munich
*)

header {* A simple formulation of First-Order Logic *}

theory First_Order_Logic imports Pure begin

text {*
  The subsequent theory development illustrates single-sorted
  intuitionistic first-order logic with equality, formulated within
  the Pure framework.  Actually this is not an example of
  Isabelle/FOL, but of Isabelle/Pure.
*}

subsection {* Syntax *}

typedecl i
typedecl o

judgment
  Trueprop :: "o \<Rightarrow> prop"    ("_" 5)


subsection {* Propositional logic *}

axiomatization
  false :: o  ("\<bottom>") and
  imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longrightarrow>" 25) and
  conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<and>" 35) and
  disj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<or>" 30)
where
  falseE [elim]: "\<bottom> \<Longrightarrow> A" and

  impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B" and
  mp [dest]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B" and

  conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" and
  conjD1: "A \<and> B \<Longrightarrow> A" and
  conjD2: "A \<and> B \<Longrightarrow> B" and

  disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C" and
  disjI1 [intro]: "A \<Longrightarrow> A \<or> B" and
  disjI2 [intro]: "B \<Longrightarrow> A \<or> B"

theorem conjE [elim]:
  assumes "A \<and> B"
  obtains A and B
proof
  from `A \<and> B` show A by (rule conjD1)
  from `A \<and> B` show B by (rule conjD2)
qed

definition
  true :: o  ("\<top>") where
  "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"

definition
  not :: "o \<Rightarrow> o"  ("\<not> _" [40] 40) where
  "\<not> A \<equiv> A \<longrightarrow> \<bottom>"

definition
  iff :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longleftrightarrow>" 25) where
  "A \<longleftrightarrow> B \<equiv> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"


theorem trueI [intro]: \<top>
proof (unfold true_def)
  show "\<bottom> \<longrightarrow> \<bottom>" ..
qed

theorem notI [intro]: "(A \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> A"
proof (unfold not_def)
  assume "A \<Longrightarrow> \<bottom>"
  then show "A \<longrightarrow> \<bottom>" ..
qed

theorem notE [elim]: "\<not> A \<Longrightarrow> A \<Longrightarrow> B"
proof (unfold not_def)
  assume "A \<longrightarrow> \<bottom>" and A
  then have \<bottom> .. then show B ..
qed

theorem iffI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B"
proof (unfold iff_def)
  assume "A \<Longrightarrow> B" then have "A \<longrightarrow> B" ..
  moreover assume "B \<Longrightarrow> A" then have "B \<longrightarrow> A" ..
  ultimately show "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)" ..
qed

theorem iff1 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"
proof (unfold iff_def)
  assume "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  then have "A \<longrightarrow> B" ..
  then show "A \<Longrightarrow> B" ..
qed

theorem iff2 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> B \<Longrightarrow> A"
proof (unfold iff_def)
  assume "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  then have "B \<longrightarrow> A" ..
  then show "B \<Longrightarrow> A" ..
qed


subsection {* Equality *}

axiomatization
  equal :: "i \<Rightarrow> i \<Rightarrow> o"  (infixl "=" 50)
where
  refl [intro]: "x = x" and
  subst: "x = y \<Longrightarrow> P x \<Longrightarrow> P y"

theorem trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

theorem sym [sym]: "x = y \<Longrightarrow> y = x"
proof -
  assume "x = y"
  from this and refl show "y = x" by (rule subst)
qed


subsection {* Quantifiers *}

axiomatization
  All :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" 10) and
  Ex :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" 10)
where
  allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x" and
  allD [dest]: "\<forall>x. P x \<Longrightarrow> P a" and
  exI [intro]: "P a \<Longrightarrow> \<exists>x. P x" and
  exE [elim]: "\<exists>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> C) \<Longrightarrow> C"


lemma "(\<exists>x. P (f x)) \<longrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then show "\<exists>y. P y"
  proof
    fix x assume "P (f x)"
    then show ?thesis ..
  qed
qed

lemma "(\<exists>x. \<forall>y. R x y) \<longrightarrow> (\<forall>y. \<exists>x. R x y)"
proof
  assume "\<exists>x. \<forall>y. R x y"
  then show "\<forall>y. \<exists>x. R x y"
  proof
    fix x assume a: "\<forall>y. R x y"
    show ?thesis
    proof
      fix y from a have "R x y" ..
      then show "\<exists>x. R x y" ..
    qed
  qed
qed

end
