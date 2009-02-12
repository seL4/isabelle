
header {* Example: First-Order Logic *}

theory %visible First_Order_Logic
imports Pure
begin

text {*
  \noindent In order to commence a new object-logic within
  Isabelle/Pure we introduce abstract syntactic categories @{text "i"}
  for individuals and @{text "o"} for object-propositions.  The latter
  is embedded into the language of Pure propositions by means of a
  separate judgment.
*}

typedecl i
typedecl o

judgment
  Trueprop :: "o \<Rightarrow> prop"    ("_" 5)

text {*
  \noindent Note that the object-logic judgement is implicit in the
  syntax: writing @{prop A} produces @{term "Trueprop A"} internally.
  From the Pure perspective this means ``@{prop A} is derivable in the
  object-logic''.
*}


subsection {* Equational reasoning \label{sec:framework-ex-equal} *}

text {*
  Equality is axiomatized as a binary predicate on individuals, with
  reflexivity as introduction, and substitution as elimination
  principle.  Note that the latter is particularly convenient in a
  framework like Isabelle, because syntactic congruences are
  implicitly produced by unification of @{term "B x"} against
  expressions containing occurrences of @{term x}.
*}

axiomatization
  equal :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "=" 50)
where
  refl [intro]: "x = x" and
  subst [elim]: "x = y \<Longrightarrow> B x \<Longrightarrow> B y"

text {*
  \noindent Substitution is very powerful, but also hard to control in
  full generality.  We derive some common symmetry~/ transitivity
  schemes of as particular consequences.
*}

theorem sym [sym]:
  assumes "x = y"
  shows "y = x"
proof -
  have "x = x" ..
  with `x = y` show "y = x" ..
qed

theorem forw_subst [trans]:
  assumes "y = x" and "B x"
  shows "B y"
proof -
  from `y = x` have "x = y" ..
  from this and `B x` show "B y" ..
qed

theorem back_subst [trans]:
  assumes "B x" and "x = y"
  shows "B y"
proof -
  from `x = y` and `B x`
  show "B y" ..
qed

theorem trans [trans]:
  assumes "x = y" and "y = z"
  shows "x = z"
proof -
  from `y = z` and `x = y`
  show "x = z" ..
qed


subsection {* Basic group theory *}

text {*
  As an example for equational reasoning we consider some bits of
  group theory.  The subsequent locale definition postulates group
  operations and axioms; we also derive some consequences of this
  specification.
*}

locale group =
  fixes prod :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<circ>" 70)
    and inv :: "i \<Rightarrow> i"  ("(_\<inverse>)" [1000] 999)
    and unit :: i  ("1")
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

text {*
  \noindent Reasoning from basic axioms is often tedious.  Our proofs
  work by producing various instances of the given rules (potentially
  the symmetric form) using the pattern ``@{command have}~@{text
  eq}~@{command "by"}~@{text "(rule r)"}'' and composing the chain of
  results via @{command also}/@{command finally}.  These steps may
  involve any of the transitivity rules declared in
  \secref{sec:framework-ex-equal}, namely @{thm trans} in combining
  the first two results in @{thm right_inv} and in the final steps of
  both proofs, @{thm forw_subst} in the first combination of @{thm
  right_unit}, and @{thm back_subst} in all other calculational steps.

  Occasional substitutions in calculations are adequate, but should
  not be over-emphasized.  The other extreme is to compose a chain by
  plain transitivity only, with replacements occurring always in
  topmost position. For example:
*}

(*<*)
theorem "\<And>A. PROP A \<Longrightarrow> PROP A"
proof -
  assume [symmetric, defn]: "\<And>x y. (x \<equiv> y) \<equiv> Trueprop (x = y)"
(*>*)
  have "x \<circ> 1 = x \<circ> (x\<inverse> \<circ> x)" unfolding left_inv ..
  also have "\<dots> = (x \<circ> x\<inverse>) \<circ> x" unfolding assoc ..
  also have "\<dots> = 1 \<circ> x" unfolding right_inv ..
  also have "\<dots> = x" unfolding left_unit ..
  finally have "x \<circ> 1 = x" .
(*<*)
qed
(*>*)

text {*
  \noindent Here we have re-used the built-in mechanism for unfolding
  definitions in order to normalize each equational problem.  A more
  realistic object-logic would include proper setup for the Simplifier
  (\secref{sec:simplifier}), the main automated tool for equational
  reasoning in Isabelle.  Then ``@{command unfolding}~@{thm
  left_inv}~@{command ".."}'' would become ``@{command "by"}~@{text
  "(simp add: left_inv)"}'' etc.
*}

end


subsection {* Propositional logic *}

text {*
  We axiomatize basic connectives of propositional logic: implication,
  disjunction, and conjunction.  The associated rules are modeled
  after Gentzen's system of Natural Deduction \cite{Gentzen:1935}.
*}

axiomatization
  imp :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<longrightarrow>" 25) where
  impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B" and
  impD [dest]: "(A \<longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"

axiomatization
  disj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<or>" 30) where
  disjE [elim]: "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C" and
  disjI\<^isub>1 [intro]: "A \<Longrightarrow> A \<or> B" and
  disjI\<^isub>2 [intro]: "B \<Longrightarrow> A \<or> B"

axiomatization
  conj :: "o \<Rightarrow> o \<Rightarrow> o"  (infixr "\<and>" 35) where
  conjI [intro]: "A \<Longrightarrow> B \<Longrightarrow> A \<and> B" and
  conjD\<^isub>1 [dest]: "A \<and> B \<Longrightarrow> A" and
  conjD\<^isub>2 [dest]: "A \<and> B \<Longrightarrow> B"

text {*
  \noindent The conjunctive destructions have the disadvantage that
  decomposing @{prop "A \<and> B"} involves an immediate decision which
  component should be projected.  The more convenient simultaneous
  elimination @{prop "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"} can be derived as
  follows:
*}

theorem conjE [elim]:
  assumes "A \<and> B"
  obtains A and B
proof
  from `A \<and> B` show A ..
  from `A \<and> B` show B ..
qed

text {*
  \noindent Here is an example of swapping conjuncts with a single
  intermediate elimination step:
*}

(*<*)
lemma "\<And>A. PROP A \<Longrightarrow> PROP A"
proof -
(*>*)
  assume "A \<and> B"
  then obtain B and A ..
  then have "B \<and> A" ..
(*<*)
qed
(*>*)

text {*
  \noindent Note that the analogous elimination rule for disjunction
  ``@{text "\<ASSUMES> A \<or> B \<OBTAINS> A \<BBAR> B"}'' coincides with
  the original axiomatization of @{thm disjE}.

  \medskip We continue propositional logic by introducing absurdity
  with its characteristic elimination.  Plain truth may then be
  defined as a proposition that is trivially true.
*}

axiomatization
  false :: o  ("\<bottom>") where
  falseE [elim]: "\<bottom> \<Longrightarrow> A"

definition
  true :: o  ("\<top>") where
  "\<top> \<equiv> \<bottom> \<longrightarrow> \<bottom>"

theorem trueI [intro]: \<top>
  unfolding true_def ..

text {*
  \medskip\noindent Now negation represents an implication towards
  absurdity:
*}

definition
  not :: "o \<Rightarrow> o"  ("\<not> _" [40] 40) where
  "\<not> A \<equiv> A \<longrightarrow> \<bottom>"

theorem notI [intro]:
  assumes "A \<Longrightarrow> \<bottom>"
  shows "\<not> A"
unfolding not_def
proof
  assume A
  then show \<bottom> by (rule `A \<Longrightarrow> \<bottom>`)
qed

theorem notE [elim]:
  assumes "\<not> A" and A
  shows B
proof -
  from `\<not> A` have "A \<longrightarrow> \<bottom>" unfolding not_def .
  from `A \<longrightarrow> \<bottom>` and `A` have \<bottom> ..
  then show B ..
qed


subsection {* Classical logic *}

text {*
  Subsequently we state the principle of classical contradiction as a
  local assumption.  Thus we refrain from forcing the object-logic
  into the classical perspective.  Within that context, we may derive
  well-known consequences of the classical principle.
*}

locale classical =
  assumes classical: "(\<not> C \<Longrightarrow> C) \<Longrightarrow> C"
begin

theorem double_negation:
  assumes "\<not> \<not> C"
  shows C
proof (rule classical)
  assume "\<not> C"
  with `\<not> \<not> C` show C ..
qed

theorem tertium_non_datur: "C \<or> \<not> C"
proof (rule double_negation)
  show "\<not> \<not> (C \<or> \<not> C)"
  proof
    assume "\<not> (C \<or> \<not> C)"
    have "\<not> C"
    proof
      assume C then have "C \<or> \<not> C" ..
      with `\<not> (C \<or> \<not> C)` show \<bottom> ..
    qed
    then have "C \<or> \<not> C" ..
    with `\<not> (C \<or> \<not> C)` show \<bottom> ..
  qed
qed

text {*
  These examples illustrate both classical reasoning and non-trivial
  propositional proofs in general.  All three rules characterize
  classical logic independently, but the original rule is already the
  most convenient to use, because it leaves the conclusion unchanged.
  Note that @{prop "(\<not> C \<Longrightarrow> C) \<Longrightarrow> C"} fits again into our format for
  eliminations, despite the additional twist that the context refers
  to the main conclusion.  So we may write @{thm classical} as the
  Isar statement ``@{text "\<OBTAINS> \<not> thesis"}''.  This also
  explains nicely how classical reasoning really works: whatever the
  main @{text thesis} might be, we may always assume its negation!
*}

end


subsection {* Quantifiers *}

text {*
  Representing quantifiers is easy, thanks to the higher-order nature
  of the underlying framework.  According to the well-known technique
  introduced by Church \cite{church40}, quantifiers are operators on
  predicates, which are syntactically represented as @{text "\<lambda>"}-terms
  of type @{typ "i \<Rightarrow> o"}.  Binder notation turns @{text "All (\<lambda>x. B
  x)"} into @{text "\<forall>x. B x"} etc.
*}

axiomatization
  All :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder "\<forall>" 10) where
  allI [intro]: "(\<And>x. B x) \<Longrightarrow> \<forall>x. B x" and
  allD [dest]: "(\<forall>x. B x) \<Longrightarrow> B a"

axiomatization
  Ex :: "(i \<Rightarrow> o) \<Rightarrow> o"  (binder "\<exists>" 10) where
  exI [intro]: "B a \<Longrightarrow> (\<exists>x. B x)" and
  exE [elim]: "(\<exists>x. B x) \<Longrightarrow> (\<And>x. B x \<Longrightarrow> C) \<Longrightarrow> C"

text {*
  \noindent The @{thm exE} rule corresponds to an Isar statement
  ``@{text "\<ASSUMES> \<exists>x. B x \<OBTAINS> x \<WHERE> B x"}''.  In the
  following example we illustrate quantifier reasoning with all four
  rules:
*}

theorem
  assumes "\<exists>x. \<forall>y. R x y"
  shows "\<forall>y. \<exists>x. R x y"
proof    -- {* @{text "\<forall>"} introduction *}
  obtain x where "\<forall>y. R x y" using `\<exists>x. \<forall>y. R x y` ..    -- {* @{text "\<exists>"} elimination *}
  fix y have "R x y" using `\<forall>y. R x y` ..    -- {* @{text "\<forall>"} destruction *}
  then show "\<exists>x. R x y" ..    -- {* @{text "\<exists>"} introduction *}
qed

end %visible
