(*  Title:      HOL/Isar_Examples/Higher_Order_Logic.thy
    Author:     Makarius
*)

section \<open>Foundations of HOL\<close>

theory Higher_Order_Logic
imports Pure
begin

text \<open>
  The following theory development demonstrates Higher-Order Logic itself,
  represented directly within the Pure framework of Isabelle. The ``HOL''
  logic given here is essentially that of Gordon @{cite "Gordon:1985:HOL"},
  although we prefer to present basic concepts in a slightly more conventional
  manner oriented towards plain Natural Deduction.
\<close>


subsection \<open>Pure Logic\<close>

class type
default_sort type

typedecl o
instance o :: type ..
instance "fun" :: (type, type) type ..


subsubsection \<open>Basic logical connectives\<close>

judgment Trueprop :: "o \<Rightarrow> prop"  ("_" 5)

axiomatization imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longrightarrow>" 25)
  where impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
    and impE [dest, trans]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"

axiomatization All :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" 10)
  where allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x"
    and allE [dest]: "\<forall>x. P x \<Longrightarrow> P a"


subsubsection \<open>Extensional equality\<close>

axiomatization equal :: "'a \<Rightarrow> 'a \<Rightarrow> o"  (infixl "=" 50)
  where refl [intro]: "x = x"
    and subst: "x = y \<Longrightarrow> P x \<Longrightarrow> P y"

abbreviation iff :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longleftrightarrow>" 25)
  where "A \<longleftrightarrow> B \<equiv> A = B"

axiomatization
  where ext [intro]: "(\<And>x. f x = g x) \<Longrightarrow> f = g"
    and iff [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B"

theorem sym [sym]:
  assumes "x = y"
  shows "y = x"
  using assms by (rule subst) (rule refl)

lemma [trans]: "x = y \<Longrightarrow> P y \<Longrightarrow> P x"
  by (rule subst) (rule sym)

lemma [trans]: "P x \<Longrightarrow> x = y \<Longrightarrow> P y"
  by (rule subst)

theorem trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

theorem iff1 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"
  by (rule subst)

theorem iff2 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> B \<Longrightarrow> A"
  by (rule subst) (rule sym)


subsubsection \<open>Derived connectives\<close>

definition false :: o  ("\<bottom>") where "\<bottom> \<equiv> \<forall>A. A"

theorem falseE [elim]:
  assumes "\<bottom>"
  shows A
proof -
  from \<open>\<bottom>\<close> have "\<forall>A. A" unfolding false_def .
  then show A ..
qed


definition true :: o  ("\<top>") where "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"

theorem trueI [intro]: \<top>
  unfolding true_def ..


definition not :: "o \<Rightarrow> o"  ("\<not> _" [40] 40)
  where "not \<equiv> \<lambda>A. A \<longrightarrow> \<bottom>"

abbreviation not_equal :: "'a \<Rightarrow> 'a \<Rightarrow> o"  (infixl "\<noteq>" 50)
  where "x \<noteq> y \<equiv> \<not> (x = y)"

theorem notI [intro]:
  assumes "A \<Longrightarrow> \<bottom>"
  shows "\<not> A"
  using assms unfolding not_def ..

theorem notE [elim]:
  assumes "\<not> A" and A
  shows B
proof -
  from \<open>\<not> A\<close> have "A \<longrightarrow> \<bottom>" unfolding not_def .
  from this and \<open>A\<close> have "\<bottom>" ..
  then show B ..
qed

lemma notE': "A \<Longrightarrow> \<not> A \<Longrightarrow> B"
  by (rule notE)

lemmas contradiction = notE notE'  \<comment> \<open>proof by contradiction in any order\<close>


definition conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<and>" 35)
  where "conj \<equiv> \<lambda>A B. \<forall>C. (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"

theorem conjI [intro]:
  assumes A and B
  shows "A \<and> B"
  unfolding conj_def
proof
  fix C
  show "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"
  proof
    assume "A \<longrightarrow> B \<longrightarrow> C"
    also note \<open>A\<close>
    also note \<open>B\<close>
    finally show C .
  qed
qed

theorem conjE [elim]:
  assumes "A \<and> B"
  obtains A and B
proof
  from \<open>A \<and> B\<close> have *: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C" for C
    unfolding conj_def ..
  show A
  proof -
    note * [of A]
    also have "A \<longrightarrow> B \<longrightarrow> A"
    proof
      assume A
      then show "B \<longrightarrow> A" ..
    qed
    finally show ?thesis .
  qed
  show B
  proof -
    note * [of B]
    also have "A \<longrightarrow> B \<longrightarrow> B"
    proof
      show "B \<longrightarrow> B" ..
    qed
    finally show ?thesis .
  qed
qed


definition disj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<or>" 30)
  where "disj \<equiv> \<lambda>A B. \<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"

theorem disjI1 [intro]:
  assumes A
  shows "A \<or> B"
  unfolding disj_def
proof
  fix C
  show "(A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  proof
    assume "A \<longrightarrow> C"
    from this and \<open>A\<close> have C ..
    then show "(B \<longrightarrow> C) \<longrightarrow> C" ..
  qed
qed

theorem disjI2 [intro]:
  assumes B
  shows "A \<or> B"
  unfolding disj_def
proof
  fix C
  show "(A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"
  proof
    show "(B \<longrightarrow> C) \<longrightarrow> C"
    proof
      assume "B \<longrightarrow> C"
      from this and \<open>B\<close> show C ..
    qed
  qed
qed

theorem disjE [elim]:
  assumes "A \<or> B"
  obtains (a) A | (b) B
proof -
  from \<open>A \<or> B\<close> have "(A \<longrightarrow> thesis) \<longrightarrow> (B \<longrightarrow> thesis) \<longrightarrow> thesis"
    unfolding disj_def ..
  also have "A \<longrightarrow> thesis"
  proof
    assume A
    then show thesis by (rule a)
  qed
  also have "B \<longrightarrow> thesis"
  proof
    assume B
    then show thesis by (rule b)
  qed
  finally show thesis .
qed


definition Ex :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" 10)
  where "\<exists>x. P x \<equiv> \<forall>C. (\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"

theorem exI [intro]: "P a \<Longrightarrow> \<exists>x. P x"
  unfolding Ex_def
proof
  fix C
  assume "P a"
  show "(\<forall>x. P x \<longrightarrow> C) \<longrightarrow> C"
  proof
    assume "\<forall>x. P x \<longrightarrow> C"
    then have "P a \<longrightarrow> C" ..
    from this and \<open>P a\<close> show C ..
  qed
qed

theorem exE [elim]:
  assumes "\<exists>x. P x"
  obtains (that) x where "P x"
proof -
  from \<open>\<exists>x. P x\<close> have "(\<forall>x. P x \<longrightarrow> thesis) \<longrightarrow> thesis"
    unfolding Ex_def ..
  also have "\<forall>x. P x \<longrightarrow> thesis"
  proof
    fix x
    show "P x \<longrightarrow> thesis"
    proof
      assume "P x"
      then show thesis by (rule that)
    qed
  qed
  finally show thesis .
qed


subsection \<open>Cantor's Theorem\<close>

text \<open>
  Cantor's Theorem states that there is no surjection from a set to its
  powerset. The subsequent formulation uses elementary \<open>\<lambda>\<close>-calculus and
  predicate logic, with standard introduction and elimination rules.
\<close>

lemma iff_contradiction:
  assumes *: "\<not> A \<longleftrightarrow> A"
  shows C
proof (rule notE)
  show "\<not> A"
  proof
    assume A
    with * have "\<not> A" ..
    from this and \<open>A\<close> show \<bottom> ..
  qed
  with * show A ..
qed

theorem Cantor: "\<not> (\<exists>f :: 'a \<Rightarrow> 'a \<Rightarrow> o. \<forall>A. \<exists>x. A = f x)"
proof
  assume "\<exists>f :: 'a \<Rightarrow> 'a \<Rightarrow> o. \<forall>A. \<exists>x. A = f x"
  then obtain f :: "'a \<Rightarrow> 'a \<Rightarrow> o" where *: "\<forall>A. \<exists>x. A = f x" ..
  let ?D = "\<lambda>x. \<not> f x x"
  from * have "\<exists>x. ?D = f x" ..
  then obtain a where "?D = f a" ..
  then have "?D a \<longleftrightarrow> f a a" using refl by (rule subst)
  then have "\<not> f a a \<longleftrightarrow> f a a" .
  then show \<bottom> by (rule iff_contradiction)
qed


subsection \<open>Classical logic\<close>

text \<open>
  The subsequent rules of classical reasoning are all equivalent.
\<close>

locale classical =
  assumes classical: "(\<not> A \<Longrightarrow> A) \<Longrightarrow> A"

theorem (in classical) Peirce's_Law: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume a: "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume A
      with \<open>\<not> A\<close> show B by (rule contradiction)
    qed
    with a show A ..
  qed
qed

theorem (in classical) double_negation:
  assumes "\<not> \<not> A"
  shows A
proof (rule classical)
  assume "\<not> A"
  with \<open>\<not> \<not> A\<close> show ?thesis by (rule contradiction)
qed

theorem (in classical) tertium_non_datur: "A \<or> \<not> A"
proof (rule double_negation)
  show "\<not> \<not> (A \<or> \<not> A)"
  proof
    assume "\<not> (A \<or> \<not> A)"
    have "\<not> A"
    proof
      assume A then have "A \<or> \<not> A" ..
      with \<open>\<not> (A \<or> \<not> A)\<close> show \<bottom> by (rule contradiction)
    qed
    then have "A \<or> \<not> A" ..
    with \<open>\<not> (A \<or> \<not> A)\<close> show \<bottom> by (rule contradiction)
  qed
qed

theorem (in classical) classical_cases:
  obtains A | "\<not> A"
  using tertium_non_datur
proof
  assume A
  then show thesis ..
next
  assume "\<not> A"
  then show thesis ..
qed

lemma
  assumes classical_cases: "\<And>A C. (A \<Longrightarrow> C) \<Longrightarrow> (\<not> A \<Longrightarrow> C) \<Longrightarrow> C"
  shows "PROP classical"
proof
  fix A
  assume *: "\<not> A \<Longrightarrow> A"
  show A
  proof (rule classical_cases)
    assume A
    then show A .
  next
    assume "\<not> A"
    then show A by (rule *)
  qed
qed

end
