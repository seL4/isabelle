(*  Title:      Pure/Examples/Higher_Order_Logic.thy
    Author:     Makarius
*)

section \<open>Foundations of HOL\<close>

theory Higher_Order_Logic
  imports Pure
begin

text \<open>
  The following theory development illustrates the foundations of Higher-Order
  Logic. The ``HOL'' logic that is given here resembles \<^cite>\<open>"Gordon:1985:HOL"\<close> and its predecessor \<^cite>\<open>"church40"\<close>, but the order of
  axiomatizations and defined connectives has be adapted to modern
  presentations of \<open>\<lambda>\<close>-calculus and Constructive Type Theory. Thus it fits
  nicely to the underlying Natural Deduction framework of Isabelle/Pure and
  Isabelle/Isar.
\<close>


section \<open>HOL syntax within Pure\<close>

class type
default_sort type

typedecl o
instance o :: type ..
instance "fun" :: (type, type) type ..

judgment Trueprop :: "o \<Rightarrow> prop"  ("_" 5)


section \<open>Minimal logic (axiomatization)\<close>

axiomatization imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longrightarrow>" 25)
  where impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
    and impE [dest, trans]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"

axiomatization All :: "('a \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" 10)
  where allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x"
    and allE [dest]: "\<forall>x. P x \<Longrightarrow> P a"

lemma atomize_imp [atomize]: "(A \<Longrightarrow> B) \<equiv> Trueprop (A \<longrightarrow> B)"
  by standard (fact impI, fact impE)

lemma atomize_all [atomize]: "(\<And>x. P x) \<equiv> Trueprop (\<forall>x. P x)"
  by standard (fact allI, fact allE)


subsubsection \<open>Derived connectives\<close>

definition False :: o
  where "False \<equiv> \<forall>A. A"

lemma FalseE [elim]:
  assumes "False"
  shows A
proof -
  from \<open>False\<close> have "\<forall>A. A" by (simp only: False_def)
  then show A ..
qed


definition True :: o
  where "True \<equiv> False \<longrightarrow> False"

lemma TrueI [intro]: True
  unfolding True_def ..


definition not :: "o \<Rightarrow> o"  ("\<not> _" [40] 40)
  where "not \<equiv> \<lambda>A. A \<longrightarrow> False"

lemma notI [intro]:
  assumes "A \<Longrightarrow> False"
  shows "\<not> A"
  using assms unfolding not_def ..

lemma notE [elim]:
  assumes "\<not> A" and A
  shows B
proof -
  from \<open>\<not> A\<close> have "A \<longrightarrow> False" by (simp only: not_def)
  from this and \<open>A\<close> have "False" ..
  then show B ..
qed

lemma notE': "A \<Longrightarrow> \<not> A \<Longrightarrow> B"
  by (rule notE)

lemmas contradiction = notE notE'  \<comment> \<open>proof by contradiction in any order\<close>


definition conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<and>" 35)
  where "A \<and> B \<equiv> \<forall>C. (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> C"

lemma conjI [intro]:
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

lemma conjE [elim]:
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
  where "A \<or> B \<equiv> \<forall>C. (A \<longrightarrow> C) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> C"

lemma disjI1 [intro]:
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

lemma disjI2 [intro]:
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

lemma disjE [elim]:
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

lemma exI [intro]: "P a \<Longrightarrow> \<exists>x. P x"
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

lemma exE [elim]:
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


subsubsection \<open>Extensional equality\<close>

axiomatization equal :: "'a \<Rightarrow> 'a \<Rightarrow> o"  (infixl "=" 50)
  where refl [intro]: "x = x"
    and subst: "x = y \<Longrightarrow> P x \<Longrightarrow> P y"

abbreviation not_equal :: "'a \<Rightarrow> 'a \<Rightarrow> o"  (infixl "\<noteq>" 50)
  where "x \<noteq> y \<equiv> \<not> (x = y)"

abbreviation iff :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longleftrightarrow>" 25)
  where "A \<longleftrightarrow> B \<equiv> A = B"

axiomatization
  where ext [intro]: "(\<And>x. f x = g x) \<Longrightarrow> f = g"
    and iff [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<longleftrightarrow> B"
  for f g :: "'a \<Rightarrow> 'b"

lemma sym [sym]: "y = x" if "x = y"
  using that by (rule subst) (rule refl)

lemma [trans]: "x = y \<Longrightarrow> P y \<Longrightarrow> P x"
  by (rule subst) (rule sym)

lemma [trans]: "P x \<Longrightarrow> x = y \<Longrightarrow> P y"
  by (rule subst)

lemma arg_cong: "f x = f y" if "x = y"
  using that by (rule subst) (rule refl)

lemma fun_cong: "f x = g x" if "f = g"
  using that by (rule subst) (rule refl)

lemma trans [trans]: "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (rule subst)

lemma iff1 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> A \<Longrightarrow> B"
  by (rule subst)

lemma iff2 [elim]: "A \<longleftrightarrow> B \<Longrightarrow> B \<Longrightarrow> A"
  by (rule subst) (rule sym)


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
    from this and \<open>A\<close> show False ..
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
  then show False by (rule iff_contradiction)
qed


subsection \<open>Characterization of Classical Logic\<close>

text \<open>
  The subsequent rules of classical reasoning are all equivalent.
\<close>

locale classical =
  assumes classical: "(\<not> A \<Longrightarrow> A) \<Longrightarrow> A"
  \<comment> \<open>predicate definition and hypothetical context\<close>
begin

lemma classical_contradiction:
  assumes "\<not> A \<Longrightarrow> False"
  shows A
proof (rule classical)
  assume "\<not> A"
  then have False by (rule assms)
  then show A ..
qed

lemma double_negation:
  assumes "\<not> \<not> A"
  shows A
proof (rule classical_contradiction)
  assume "\<not> A"
  with \<open>\<not> \<not> A\<close> show False by (rule contradiction)
qed

lemma tertium_non_datur: "A \<or> \<not> A"
proof (rule double_negation)
  show "\<not> \<not> (A \<or> \<not> A)"
  proof
    assume "\<not> (A \<or> \<not> A)"
    have "\<not> A"
    proof
      assume A then have "A \<or> \<not> A" ..
      with \<open>\<not> (A \<or> \<not> A)\<close> show False by (rule contradiction)
    qed
    then have "A \<or> \<not> A" ..
    with \<open>\<not> (A \<or> \<not> A)\<close> show False by (rule contradiction)
  qed
qed

lemma classical_cases:
  obtains A | "\<not> A"
  using tertium_non_datur
proof
  assume A
  then show thesis ..
next
  assume "\<not> A"
  then show thesis ..
qed

end

lemma classical_if_cases: classical
  if cases: "\<And>A C. (A \<Longrightarrow> C) \<Longrightarrow> (\<not> A \<Longrightarrow> C) \<Longrightarrow> C"
proof
  fix A
  assume *: "\<not> A \<Longrightarrow> A"
  show A
  proof (rule cases)
    assume A
    then show A .
  next
    assume "\<not> A"
    then show A by (rule *)
  qed
qed


section \<open>Peirce's Law\<close>

text \<open>
  Peirce's Law is another characterization of classical reasoning. Its
  statement only requires implication.
\<close>

theorem (in classical) Peirce's_Law: "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume *: "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume A
      with \<open>\<not> A\<close> show B by (rule contradiction)
    qed
    with * show A ..
  qed
qed


section \<open>Hilbert's choice operator (axiomatization)\<close>

axiomatization Eps :: "('a \<Rightarrow> o) \<Rightarrow> 'a"
  where someI: "P x \<Longrightarrow> P (Eps P)"

syntax "_Eps" :: "pttrn \<Rightarrow> o \<Rightarrow> 'a"  ("(3SOME _./ _)" [0, 10] 10)
syntax_consts "_Eps" \<rightleftharpoons> Eps
translations "SOME x. P" \<rightleftharpoons> "CONST Eps (\<lambda>x. P)"

text \<open>
  \<^medskip>
  It follows a derivation of the classical law of tertium-non-datur by
  means of Hilbert's choice operator (due to Berghofer, Beeson, Harrison,
  based on a proof by Diaconescu).
  \<^medskip>
\<close>

theorem Diaconescu: "A \<or> \<not> A"
proof -
  let ?P = "\<lambda>x. (A \<and> x) \<or> \<not> x"
  let ?Q = "\<lambda>x. (A \<and> \<not> x) \<or> x"

  have a: "?P (Eps ?P)"
  proof (rule someI)
    have "\<not> False" ..
    then show "?P False" ..
  qed
  have b: "?Q (Eps ?Q)"
  proof (rule someI)
    have True ..
    then show "?Q True" ..
  qed

  from a show ?thesis
  proof
    assume "A \<and> Eps ?P"
    then have A ..
    then show ?thesis ..
  next
    assume "\<not> Eps ?P"
    from b show ?thesis
    proof
      assume "A \<and> \<not> Eps ?Q"
      then have A ..
      then show ?thesis ..
    next
      assume "Eps ?Q"
      have neq: "?P \<noteq> ?Q"
      proof
        assume "?P = ?Q"
        then have "Eps ?P \<longleftrightarrow> Eps ?Q" by (rule arg_cong)
        also note \<open>Eps ?Q\<close>
        finally have "Eps ?P" .
        with \<open>\<not> Eps ?P\<close> show False by (rule contradiction)
      qed
      have "\<not> A"
      proof
        assume A
        have "?P = ?Q"
        proof (rule ext)
          show "?P x \<longleftrightarrow> ?Q x" for x
          proof
            assume "?P x"
            then show "?Q x"
            proof
              assume "\<not> x"
              with \<open>A\<close> have "A \<and> \<not> x" ..
              then show ?thesis ..
            next
              assume "A \<and> x"
              then have x ..
              then show ?thesis ..
            qed
          next
            assume "?Q x"
            then show "?P x"
            proof
              assume "A \<and> \<not> x"
              then have "\<not> x" ..
              then show ?thesis ..
            next
              assume x
              with \<open>A\<close> have "A \<and> x" ..
              then show ?thesis ..
            qed
          qed
        qed
        with neq show False by (rule contradiction)
      qed
      then show ?thesis ..
    qed
  qed
qed

text \<open>
  This means, the hypothetical predicate \<^const>\<open>classical\<close> always holds
  unconditionally (with all consequences).
\<close>

interpretation classical
proof (rule classical_if_cases)
  fix A C
  assume *: "A \<Longrightarrow> C"
    and **: "\<not> A \<Longrightarrow> C"
  from Diaconescu [of A] show C
  proof
    assume A
    then show C by (rule *)
  next
    assume "\<not> A"
    then show C by (rule **)
  qed
qed

thm classical
  classical_contradiction
  double_negation
  tertium_non_datur
  classical_cases
  Peirce's_Law

end
