(*  Title:      FOL/ex/First_Order_Logic.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Munich
*)

header {* A simple formulation of First-Order Logic *}

theory First_Order_Logic = Pure:

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

consts
  false :: o    ("\<bottom>")
  imp :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<longrightarrow>" 25)
  conj :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<and>" 35)
  disj :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<or>" 30)

axioms
  falseE [elim]: "\<bottom> \<Longrightarrow> A"

  impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
  mp [dest]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"

  conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  conjD1: "A \<and> B \<Longrightarrow> A"
  conjD2: "A \<and> B \<Longrightarrow> B"

  disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"
  disjI1 [intro]: "A \<Longrightarrow> A \<or> B"
  disjI2 [intro]: "B \<Longrightarrow> A \<or> B"

theorem conjE [elim]: "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
proof -
  assume ab: "A \<and> B"
  assume r: "A \<Longrightarrow> B \<Longrightarrow> C"
  show C
  proof (rule r)
    from ab show A by (rule conjD1)
    from ab show B by (rule conjD2)
  qed
qed

constdefs
  true :: o    ("\<top>")
  "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"
  not :: "o \<Rightarrow> o"    ("\<not> _" [40] 40)
  "\<not> A \<equiv> A \<longrightarrow> \<bottom>"
  iff :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<longleftrightarrow>" 25)
  "A \<longleftrightarrow> B \<equiv> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"


theorem trueI [intro]: \<top>
proof (unfold true_def)
  show "\<bottom> \<longrightarrow> \<bottom>" ..
qed

theorem notI [intro]: "(A \<Longrightarrow> \<bottom>) \<Longrightarrow> \<not> A"
proof (unfold not_def)
  assume "A \<Longrightarrow> \<bottom>"
  thus "A \<longrightarrow> \<bottom>" ..
qed

theorem notE [elim]: "\<not> A \<Longrightarrow> A \<Longrightarrow> B"
proof (unfold not_def)
  assume "A \<longrightarrow> \<bottom>" and A
  hence \<bottom> .. thus B ..
qed

theorem iffI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B"
proof (unfold iff_def)
  assume "A \<Longrightarrow> B" hence "A \<longrightarrow> B" ..
  moreover assume "B \<Longrightarrow> A" hence "B \<longrightarrow> A" ..
  ultimately show "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)" ..
qed

theorem iff1 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"
proof (unfold iff_def)
  assume "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  hence "A \<longrightarrow> B" ..
  thus "A \<Longrightarrow> B" ..
qed

theorem iff2 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> B \<Longrightarrow> A"
proof (unfold iff_def)
  assume "(A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  hence "B \<longrightarrow> A" ..
  thus "B \<Longrightarrow> A" ..
qed


subsection {* Equality *}

consts
  equal :: "i \<Rightarrow> i \<Rightarrow> o"    (infixl "=" 50)

axioms
  refl [intro]: "x = x"
  subst: "x = y \<Longrightarrow> P(x) \<Longrightarrow> P(y)"

theorem trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

theorem sym [sym]: "x = y \<Longrightarrow> y = x"
proof -
  assume "x = y"
  from this and refl show "y = x" by (rule subst)
qed


subsection {* Quantifiers *}

consts
  All :: "(i \<Rightarrow> o) \<Rightarrow> o"    (binder "\<forall>" 10)
  Ex :: "(i \<Rightarrow> o) \<Rightarrow> o"    (binder "\<exists>" 10)

axioms
  allI [intro]: "(\<And>x. P(x)) \<Longrightarrow> \<forall>x. P(x)"
  allD [dest]: "\<forall>x. P(x) \<Longrightarrow> P(a)"

  exI [intro]: "P(a) \<Longrightarrow> \<exists>x. P(x)"
  exE [elim]: "\<exists>x. P(x) \<Longrightarrow> (\<And>x. P(x) \<Longrightarrow> C) \<Longrightarrow> C"


lemma "(\<exists>x. P(f(x))) \<longrightarrow> (\<exists>y. P(y))"
proof
  assume "\<exists>x. P(f(x))"
  thus "\<exists>y. P(y)"
  proof
    fix x assume "P(f(x))"
    thus ?thesis ..
  qed
qed

lemma "(\<exists>x. \<forall>y. R(x, y)) \<longrightarrow> (\<forall>y. \<exists>x. R(x, y))"
proof
  assume "\<exists>x. \<forall>y. R(x, y)"
  thus "\<forall>y. \<exists>x. R(x, y)"
  proof
    fix x assume a: "\<forall>y. R(x, y)"
    show ?thesis
    proof
      fix y from a have "R(x, y)" ..
      thus "\<exists>x. R(x, y)" ..
    qed
  qed
qed

end
