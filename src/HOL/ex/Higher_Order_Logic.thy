(*  Title:      HOL/ex/Higher_Order_Logic.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Foundations of HOL *}

theory Higher_Order_Logic = CPure:

text {*
  The following theory development demonstrates Higher-Order Logic
  itself, represented directly within the Pure framework of Isabelle.
  The ``HOL'' logic given here is essentially that of Gordon
  \cite{Gordon:1985:HOL}, although we prefer to present basic concepts
  in a slightly more conventional manner oriented towards plain
  Natural Deduction.
*}


subsection {* Pure Logic *}

classes type
defaultsort type

typedecl o
arities
  o :: type
  fun :: (type, type) type


subsubsection {* Basic logical connectives *}

judgment
  Trueprop :: "o \<Rightarrow> prop"    ("_" 5)

consts
  imp :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<longrightarrow>" 25)
  All :: "('a \<Rightarrow> o) \<Rightarrow> o"    (binder "\<forall>" 10)

axioms
  impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
  impE [dest, trans]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"
  allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x"
  allE [dest]: "\<forall>x. P x \<Longrightarrow> P a"


subsubsection {* Extensional equality *}

consts
  equal :: "'a \<Rightarrow> 'a \<Rightarrow> o"   (infixl "=" 50)

axioms
  refl [intro]: "x = x"
  subst: "x = y \<Longrightarrow> P x \<Longrightarrow> P y"
  ext [intro]: "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  iff [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A = B"

theorem sym [sym]: "x = y \<Longrightarrow> y = x"
proof -
  assume "x = y"
  thus "y = x" by (rule subst) (rule refl)
qed

lemma [trans]: "x = y \<Longrightarrow> P y \<Longrightarrow> P x"
  by (rule subst) (rule sym)

lemma [trans]: "P x \<Longrightarrow> x = y \<Longrightarrow> P y"
  by (rule subst)

theorem trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

theorem iff1 [elim]: "A = B \<Longrightarrow> A \<Longrightarrow> B"
  by (rule subst)

theorem iff2 [elim]: "A = B \<Longrightarrow> B \<Longrightarrow> A"
  by (rule subst) (rule sym)


subsubsection {* Derived connectives *}

constdefs
  false :: o    ("\<bottom>")
  "\<bottom> \<equiv> \<forall>A. A"
  true :: o    ("\<top>")
  "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"
  not :: "o \<Rightarrow> o"     ("\<not> _" [40] 40)
  "not \<equiv> \<lambda>A. A \<longrightarrow> \<bottom>"
  conj :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<and>" 35)
  "conj \<equiv> \<lambda>A B. \<forall>C. (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"
  disj :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<or>" 30)
  "disj \<equiv> \<lambda>A B. \<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  Ex :: "('a \<Rightarrow> o) \<Rightarrow> o"    (binder "\<exists>" 10)
  "Ex \<equiv> \<lambda>P. \<forall>C. (\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"

syntax
  "_not_equal" :: "'a \<Rightarrow> 'a \<Rightarrow> o"    (infixl "\<noteq>" 50)
translations
  "x \<noteq> y"  \<rightleftharpoons>  "\<not> (x = y)"

theorem falseE [elim]: "\<bottom> \<Longrightarrow> A"
proof (unfold false_def)
  assume "\<forall>A. A"
  thus A ..
qed

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
  assume "A \<longrightarrow> \<bottom>"
  also assume A
  finally have \<bottom> ..
  thus B ..
qed

lemma notE': "A \<Longrightarrow> \<not> A \<Longrightarrow> B"
  by (rule notE)

lemmas contradiction = notE notE'  -- {* proof by contradiction in any order *}

theorem conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
proof (unfold conj_def)
  assume A and B
  show "\<forall>C. (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"
  proof
    fix C show "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"
    proof
      assume "A \<longrightarrow> B \<longrightarrow> C"
      also have A .
      also have B .
      finally show C .
    qed
  qed
qed

theorem conjE [elim]: "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
proof (unfold conj_def)
  assume c: "\<forall>C. (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"
  assume "A \<Longrightarrow> B \<Longrightarrow> C"
  moreover {
    from c have "(A \<longrightarrow> B \<longrightarrow> A) \<longrightarrow> A" ..
    also have "A \<longrightarrow> B \<longrightarrow> A"
    proof
      assume A
      thus "B \<longrightarrow> A" ..
    qed
    finally have A .
  } moreover {
    from c have "(A \<longrightarrow> B \<longrightarrow> B) \<longrightarrow> B" ..
    also have "A \<longrightarrow> B \<longrightarrow> B"
    proof
      show "B \<longrightarrow> B" ..
    qed
    finally have B .
  } ultimately show C .
qed

theorem disjI1 [intro]: "A \<Longrightarrow> A \<or> B"
proof (unfold disj_def)
  assume A
  show "\<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  proof
    fix C show "(A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
    proof
      assume "A \<longrightarrow> C"
      also have A .
      finally have C .
      thus "(B \<longrightarrow> C) \<longrightarrow> C" ..
    qed
  qed
qed

theorem disjI2 [intro]: "B \<Longrightarrow> A \<or> B"
proof (unfold disj_def)
  assume B
  show "\<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  proof
    fix C show "(A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
    proof
      show "(B \<longrightarrow> C) \<longrightarrow> C"
      proof
        assume "B \<longrightarrow> C"
        also have B .
        finally show C .
      qed
    qed
  qed
qed

theorem disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"
proof (unfold disj_def)
  assume c: "\<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  assume r1: "A \<Longrightarrow> C" and r2: "B \<Longrightarrow> C"
  from c have "(A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C" ..
  also have "A \<longrightarrow> C"
  proof
    assume A thus C by (rule r1)
  qed
  also have "B \<longrightarrow> C"
  proof
    assume B thus C by (rule r2)
  qed
  finally show C .
qed

theorem exI [intro]: "P a \<Longrightarrow> \<exists>x. P x"
proof (unfold Ex_def)
  assume "P a"
  show "\<forall>C. (\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"
  proof
    fix C show "(\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"
    proof
      assume "\<forall>x. P x \<longrightarrow> C"
      hence "P a \<longrightarrow> C" ..
      also have "P a" .
      finally show C .
    qed
  qed
qed

theorem exE [elim]: "\<exists>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> C) \<Longrightarrow> C"
proof (unfold Ex_def)
  assume c: "\<forall>C. (\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"
  assume r: "\<And>x. P x \<Longrightarrow> C"
  from c have "(\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C" ..
  also have "\<forall>x. P x \<longrightarrow> C"
  proof
    fix x show "P x \<longrightarrow> C"
    proof
      assume "P x"
      thus C by (rule r)
    qed
  qed
  finally show C .
qed


subsection {* Classical logic *}

locale classical =
  assumes classical: "(\<not> A \<Longrightarrow> A) \<Longrightarrow> A"

theorem (in classical)
  Peirce's_Law: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume a: "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume A
      thus B by (rule contradiction)
    qed
    with a show A ..
  qed
qed

theorem (in classical)
  double_negation: "\<not> \<not> A \<Longrightarrow> A"
proof -
  assume "\<not> \<not> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    thus ?thesis by (rule contradiction)
  qed
qed

theorem (in classical)
  tertium_non_datur: "A \<or> \<not> A"
proof (rule double_negation)
  show "\<not> \<not> (A \<or> \<not> A)"
  proof
    assume "\<not> (A \<or> \<not> A)"
    have "\<not> A"
    proof
      assume A hence "A \<or> \<not> A" ..
      thus \<bottom> by (rule contradiction)
    qed
    hence "A \<or> \<not> A" ..
    thus \<bottom> by (rule contradiction)
  qed
qed

theorem (in classical)
  classical_cases: "(A \<Longrightarrow> C) \<Longrightarrow> (\<not> A \<Longrightarrow> C) \<Longrightarrow> C"
proof -
  assume r1: "A \<Longrightarrow> C" and r2: "\<not> A \<Longrightarrow> C"
  from tertium_non_datur show C
  proof
    assume A
    thus ?thesis by (rule r1)
  next
    assume "\<not> A"
    thus ?thesis by (rule r2)
  qed
qed

lemma (in classical) "(\<not> A \<Longrightarrow> A) \<Longrightarrow> A"  (* FIXME *)
proof -
  assume r: "\<not> A \<Longrightarrow> A"
  show A
  proof (rule classical_cases)
    assume A thus A .
  next
    assume "\<not> A" thus A by (rule r)
  qed
qed

end
