(*:maxLineLen=78:*)

section \<open>Example: First-Order Logic\<close>

theory %visible First_Order_Logic
imports Base  (* FIXME Pure!? *)
begin

text \<open>
  In order to commence a new object-logic within Isabelle/Pure we introduce
  abstract syntactic categories \<open>i\<close> for individuals and \<open>o\<close> for
  object-propositions. The latter is embedded into the language of Pure
  propositions by means of a separate judgment.
\<close>

typedecl i
typedecl o

judgment Trueprop :: "o \<Rightarrow> prop"    (\<open>_\<close> 5)

text \<open>
  Note that the object-logic judgment is implicit in the syntax: writing
  \<^prop>\<open>A\<close> produces \<^term>\<open>Trueprop A\<close> internally. From the Pure
  perspective this means ``\<^prop>\<open>A\<close> is derivable in the object-logic''.
\<close>


subsection \<open>Equational reasoning \label{sec:framework-ex-equal}\<close>

text \<open>
  Equality is axiomatized as a binary predicate on individuals, with
  reflexivity as introduction, and substitution as elimination principle. Note
  that the latter is particularly convenient in a framework like Isabelle,
  because syntactic congruences are implicitly produced by unification of
  \<open>B x\<close> against expressions containing occurrences of \<open>x\<close>.
\<close>

axiomatization equal :: "i \<Rightarrow> i \<Rightarrow> o"  (infix \<open>=\<close> 50)
  where refl [intro]: "x = x"
    and subst [elim]: "x = y \<Longrightarrow> B x \<Longrightarrow> B y"

text \<open>
  Substitution is very powerful, but also hard to control in full generality.
  We derive some common symmetry~/ transitivity schemes of \<^term>\<open>equal\<close> as
  particular consequences.
\<close>

theorem sym [sym]:
  assumes "x = y"
  shows "y = x"
proof -
  have "x = x" ..
  with \<open>x = y\<close> show "y = x" ..
qed

theorem forw_subst [trans]:
  assumes "y = x" and "B x"
  shows "B y"
proof -
  from \<open>y = x\<close> have "x = y" ..
  from this and \<open>B x\<close> show "B y" ..
qed

theorem back_subst [trans]:
  assumes "B x" and "x = y"
  shows "B y"
proof -
  from \<open>x = y\<close> and \<open>B x\<close>
  show "B y" ..
qed

theorem trans [trans]:
  assumes "x = y" and "y = z"
  shows "x = z"
proof -
  from \<open>y = z\<close> and \<open>x = y\<close>
  show "x = z" ..
qed


subsection \<open>Basic group theory\<close>

text \<open>
  As an example for equational reasoning we consider some bits of group
  theory. The subsequent locale definition postulates group operations and
  axioms; we also derive some consequences of this specification.
\<close>

locale group =
  fixes prod :: "i \<Rightarrow> i \<Rightarrow> i"  (infix \<open>\<circ>\<close> 70)
    and inv :: "i \<Rightarrow> i"  (\<open>(_\<inverse>)\<close> [1000] 999)
    and unit :: i  (\<open>1\<close>)
  assumes assoc: "(x \<circ> y) \<circ> z = x \<circ> (y \<circ> z)"
    and left_unit:  "1 \<circ> x = x"
    and left_inv: "x\<inverse> \<circ> x = 1"
begin

theorem right_inv: "x \<circ> x\<inverse> = 1"
proof -
  have "x \<circ> x\<inverse> = 1 \<circ> (x \<circ> x\<inverse>)" by (rule left_unit [symmetric])
  also have "\<dots> = (1 \<circ> x) \<circ> x\<inverse>" by (rule assoc [symmetric])
  also have "1 = (x\<inverse>)\<inverse> \<circ> x\<inverse>" by (rule left_inv [symmetric])
  also have "\<dots> \<circ> x = (x\<inverse>)\<inverse> \<circ> (x\<inverse> \<circ> x)" by (rule assoc)
  also have "x\<inverse> \<circ> x = 1" by (rule left_inv)
  also have "((x\<inverse>)\<inverse> \<circ> \<dots>) \<circ> x\<inverse> = (x\<inverse>)\<inverse> \<circ> (1 \<circ> x\<inverse>)" by (rule assoc)
  also have "1 \<circ> x\<inverse> = x\<inverse>" by (rule left_unit)
  also have "(x\<inverse>)\<inverse> \<circ> \<dots> = 1" by (rule left_inv)
  finally show "x \<circ> x\<inverse> = 1" .
qed

theorem right_unit: "x \<circ> 1 = x"
proof -
  have "1 = x\<inverse> \<circ> x" by (rule left_inv [symmetric])
  also have "x \<circ> \<dots> = (x \<circ> x\<inverse>) \<circ> x" by (rule assoc [symmetric])
  also have "x \<circ> x\<inverse> = 1" by (rule right_inv)
  also have "\<dots> \<circ> x = x" by (rule left_unit)
  finally show "x \<circ> 1 = x" .
qed

text \<open>
  Reasoning from basic axioms is often tedious. Our proofs work by producing
  various instances of the given rules (potentially the symmetric form) using
  the pattern ``\<^theory_text>\<open>have eq by (rule r)\<close>'' and composing the chain of results
  via \<^theory_text>\<open>also\<close>/\<^theory_text>\<open>finally\<close>. These steps may involve any of the transitivity
  rules declared in \secref{sec:framework-ex-equal}, namely @{thm trans} in
  combining the first two results in @{thm right_inv} and in the final steps
  of both proofs, @{thm forw_subst} in the first combination of @{thm
  right_unit}, and @{thm back_subst} in all other calculational steps.

  Occasional substitutions in calculations are adequate, but should not be
  over-emphasized. The other extreme is to compose a chain by plain
  transitivity only, with replacements occurring always in topmost position.
  For example:
\<close>

(*<*)
theorem "\<And>A. PROP A \<Longrightarrow> PROP A"
proof -
  assume [symmetric, defn]: "\<And>x y. (x \<equiv> y) \<equiv> Trueprop (x = y)"
  fix x
(*>*)
  have "x \<circ> 1 = x \<circ> (x\<inverse> \<circ> x)" unfolding left_inv ..
  also have "\<dots> = (x \<circ> x\<inverse>) \<circ> x" unfolding assoc ..
  also have "\<dots> = 1 \<circ> x" unfolding right_inv ..
  also have "\<dots> = x" unfolding left_unit ..
  finally have "x \<circ> 1 = x" .
(*<*)
qed
(*>*)

text \<open>
  Here we have re-used the built-in mechanism for unfolding definitions in
  order to normalize each equational problem. A more realistic object-logic
  would include proper setup for the Simplifier (\secref{sec:simplifier}), the
  main automated tool for equational reasoning in Isabelle. Then ``\<^theory_text>\<open>unfolding
  left_inv ..\<close>'' would become ``\<^theory_text>\<open>by (simp only: left_inv)\<close>'' etc.
\<close>

end


subsection \<open>Propositional logic \label{sec:framework-ex-prop}\<close>

text \<open>
  We axiomatize basic connectives of propositional logic: implication,
  disjunction, and conjunction. The associated rules are modeled after
  Gentzen's system of Natural Deduction \<^cite>\<open>"Gentzen:1935"\<close>.
\<close>

axiomatization imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<longrightarrow>\<close> 25)
  where impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B"
    and impD [dest]: "(A \<longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"

axiomatization disj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<or>\<close> 30)
  where disjI\<^sub>1 [intro]: "A \<Longrightarrow> A \<or> B"
    and disjI\<^sub>2 [intro]: "B \<Longrightarrow> A \<or> B"
    and disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"

axiomatization conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr \<open>\<and>\<close> 35)
  where conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    and conjD\<^sub>1: "A \<and> B \<Longrightarrow> A"
    and conjD\<^sub>2: "A \<and> B \<Longrightarrow> B"

text \<open>
  The conjunctive destructions have the disadvantage that decomposing \<^prop>\<open>A \<and> B\<close> involves an immediate decision which component should be projected.
  The more convenient simultaneous elimination \<^prop>\<open>A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow>
  C\<close> can be derived as follows:
\<close>

theorem conjE [elim]:
  assumes "A \<and> B"
  obtains A and B
proof
  from \<open>A \<and> B\<close> show A by (rule conjD\<^sub>1)
  from \<open>A \<and> B\<close> show B by (rule conjD\<^sub>2)
qed

text \<open>
  Here is an example of swapping conjuncts with a single intermediate
  elimination step:
\<close>

(*<*)
lemma "\<And>A. PROP A \<Longrightarrow> PROP A"
proof -
  fix A B
(*>*)
  assume "A \<and> B"
  then obtain B and A ..
  then have "B \<and> A" ..
(*<*)
qed
(*>*)

text \<open>
  Note that the analogous elimination rule for disjunction ``\<^theory_text>\<open>assumes "A \<or> B"
  obtains A \<BBAR> B\<close>'' coincides with the original axiomatization of @{thm
  disjE}.

  \<^medskip>
  We continue propositional logic by introducing absurdity with its
  characteristic elimination. Plain truth may then be defined as a proposition
  that is trivially true.
\<close>

axiomatization false :: o  (\<open>\<bottom>\<close>)
  where falseE [elim]: "\<bottom> \<Longrightarrow> A"

definition true :: o  (\<open>\<top>\<close>)
  where "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"

theorem trueI [intro]: \<top>
  unfolding true_def ..

text \<open>
  \<^medskip>
  Now negation represents an implication towards absurdity:
\<close>

definition not :: "o \<Rightarrow> o"  (\<open>\<not> _\<close> [40] 40)
  where "\<not> A \<equiv> A \<longrightarrow> \<bottom>"

theorem notI [intro]:
  assumes "A \<Longrightarrow> \<bottom>"
  shows "\<not> A"
unfolding not_def
proof
  assume A
  then show \<bottom> by (rule \<open>A \<Longrightarrow> \<bottom>\<close>)
qed

theorem notE [elim]:
  assumes "\<not> A" and A
  shows B
proof -
  from \<open>\<not> A\<close> have "A \<longrightarrow> \<bottom>" unfolding not_def .
  from \<open>A \<longrightarrow> \<bottom>\<close> and \<open>A\<close> have \<bottom> ..
  then show B ..
qed


subsection \<open>Classical logic\<close>

text \<open>
  Subsequently we state the principle of classical contradiction as a local
  assumption. Thus we refrain from forcing the object-logic into the classical
  perspective. Within that context, we may derive well-known consequences of
  the classical principle.
\<close>

locale classical =
  assumes classical: "(\<not> C \<Longrightarrow> C) \<Longrightarrow> C"
begin

theorem double_negation:
  assumes "\<not> \<not> C"
  shows C
proof (rule classical)
  assume "\<not> C"
  with \<open>\<not> \<not> C\<close> show C ..
qed

theorem tertium_non_datur: "C \<or> \<not> C"
proof (rule double_negation)
  show "\<not> \<not> (C \<or> \<not> C)"
  proof
    assume "\<not> (C \<or> \<not> C)"
    have "\<not> C"
    proof
      assume C then have "C \<or> \<not> C" ..
      with \<open>\<not> (C \<or> \<not> C)\<close> show \<bottom> ..
    qed
    then have "C \<or> \<not> C" ..
    with \<open>\<not> (C \<or> \<not> C)\<close> show \<bottom> ..
  qed
qed

text \<open>
  These examples illustrate both classical reasoning and non-trivial
  propositional proofs in general. All three rules characterize classical
  logic independently, but the original rule is already the most convenient to
  use, because it leaves the conclusion unchanged. Note that \<^prop>\<open>(\<not> C \<Longrightarrow> C)
  \<Longrightarrow> C\<close> fits again into our format for eliminations, despite the additional
  twist that the context refers to the main conclusion. So we may write @{thm
  classical} as the Isar statement ``\<^theory_text>\<open>obtains \<not> thesis\<close>''. This also explains
  nicely how classical reasoning really works: whatever the main \<open>thesis\<close>
  might be, we may always assume its negation!
\<close>

end


subsection \<open>Quantifiers \label{sec:framework-ex-quant}\<close>

text \<open>
  Representing quantifiers is easy, thanks to the higher-order nature of the
  underlying framework. According to the well-known technique introduced by
  Church \<^cite>\<open>"church40"\<close>, quantifiers are operators on predicates, which
  are syntactically represented as \<open>\<lambda>\<close>-terms of type \<^typ>\<open>i \<Rightarrow> o\<close>. Binder
  notation turns \<open>All (\<lambda>x. B x)\<close> into \<open>\<forall>x. B x\<close> etc.
\<close>

axiomatization All :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder \<open>\<forall>\<close> 10)
  where allI [intro]: "(\<And>x. B x) \<Longrightarrow> \<forall>x. B x"
    and allD [dest]: "(\<forall>x. B x) \<Longrightarrow> B a"

axiomatization Ex :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder \<open>\<exists>\<close> 10)
  where exI [intro]: "B a \<Longrightarrow> (\<exists>x. B x)"
    and exE [elim]: "(\<exists>x. B x) \<Longrightarrow> (\<And>x. B x \<Longrightarrow> C) \<Longrightarrow> C"

text \<open>
  The statement of @{thm exE} corresponds to ``\<^theory_text>\<open>assumes "\<exists>x. B x" obtains x
  where "B x"\<close>'' in Isar. In the subsequent example we illustrate quantifier
  reasoning involving all four rules:
\<close>

theorem
  assumes "\<exists>x. \<forall>y. R x y"
  shows "\<forall>y. \<exists>x. R x y"
proof    \<comment> \<open>\<open>\<forall>\<close> introduction\<close>
  obtain x where "\<forall>y. R x y" using \<open>\<exists>x. \<forall>y. R x y\<close> ..    \<comment> \<open>\<open>\<exists>\<close> elimination\<close>
  fix y have "R x y" using \<open>\<forall>y. R x y\<close> ..    \<comment> \<open>\<open>\<forall>\<close> destruction\<close>
  then show "\<exists>x. R x y" ..    \<comment> \<open>\<open>\<exists>\<close> introduction\<close>
qed


subsection \<open>Canonical reasoning patterns\<close>

text \<open>
  The main rules of first-order predicate logic from
  \secref{sec:framework-ex-prop} and \secref{sec:framework-ex-quant} can now
  be summarized as follows, using the native Isar statement format of
  \secref{sec:framework-stmt}.

  \<^medskip>
  \begin{tabular}{l}
  \<^theory_text>\<open>impI: assumes "A \<Longrightarrow> B" shows "A \<longrightarrow> B"\<close> \\
  \<^theory_text>\<open>impD: assumes "A \<longrightarrow> B" and A shows B\<close> \\[1ex]

  \<^theory_text>\<open>disjI\<^sub>1: assumes A shows "A \<or> B"\<close> \\
  \<^theory_text>\<open>disjI\<^sub>2: assumes B shows "A \<or> B"\<close> \\
  \<^theory_text>\<open>disjE: assumes "A \<or> B" obtains A \<BBAR> B\<close> \\[1ex]

  \<^theory_text>\<open>conjI: assumes A and B shows A \<and> B\<close> \\
  \<^theory_text>\<open>conjE: assumes "A \<and> B" obtains A and B\<close> \\[1ex]

  \<^theory_text>\<open>falseE: assumes \<bottom> shows A\<close> \\
  \<^theory_text>\<open>trueI: shows \<top>\<close> \\[1ex]

  \<^theory_text>\<open>notI: assumes "A \<Longrightarrow> \<bottom>" shows "\<not> A"\<close> \\
  \<^theory_text>\<open>notE: assumes "\<not> A" and A shows B\<close> \\[1ex]

  \<^theory_text>\<open>allI: assumes "\<And>x. B x" shows "\<forall>x. B x"\<close> \\
  \<^theory_text>\<open>allE: assumes "\<forall>x. B x" shows "B a"\<close> \\[1ex]

  \<^theory_text>\<open>exI: assumes "B a" shows "\<exists>x. B x"\<close> \\
  \<^theory_text>\<open>exE: assumes "\<exists>x. B x" obtains a where "B a"\<close>
  \end{tabular}
  \<^medskip>

  This essentially provides a declarative reading of Pure rules as Isar
  reasoning patterns: the rule statements tells how a canonical proof outline
  shall look like. Since the above rules have already been declared as
  @{attribute (Pure) intro}, @{attribute (Pure) elim}, @{attribute (Pure)
  dest} --- each according to its particular shape --- we can immediately
  write Isar proof texts as follows:
\<close>

(*<*)
theorem "\<And>A. PROP A \<Longrightarrow> PROP A"
proof -
(*>*)

  text_raw \<open>\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "A \<longrightarrow> B"
  proof
    assume A
    show B \<proof>
  qed

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "A \<longrightarrow> B" and A \<proof>
  then have B ..

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have A \<proof>
  then have "A \<or> B" ..

  have B \<proof>
  then have "A \<or> B" ..

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "A \<or> B" \<proof>
  then have C
  proof
    assume A
    then show C \<proof>
  next
    assume B
    then show C \<proof>
  qed

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have A and B \<proof>
  then have "A \<and> B" ..

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "A \<and> B" \<proof>
  then obtain A and B ..

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<bottom>" \<proof>
  then have A ..

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<top>" ..

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<not> A"
  proof
    assume A
    then show "\<bottom>" \<proof>
  qed

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<not> A" and A \<proof>
  then have B ..

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<forall>x. B x"
  proof
    fix x
    show "B x" \<proof>
  qed

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<forall>x. B x" \<proof>
  then have "B a" ..

  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<exists>x. B x"
  proof
    show "B a" \<proof>
  qed

  text_raw \<open>\end{minipage}\qquad\begin{minipage}[t]{0.4\textwidth}\<close>(*<*)next(*>*)

  have "\<exists>x. B x" \<proof>
  then obtain a where "B a" ..

  text_raw \<open>\end{minipage}\<close>

(*<*)
qed
(*>*)

text \<open>
  \<^bigskip>
  Of course, these proofs are merely examples. As sketched in
  \secref{sec:framework-subproof}, there is a fair amount of flexibility in
  expressing Pure deductions in Isar. Here the user is asked to express
  himself adequately, aiming at proof texts of literary quality.
\<close>

end %visible
