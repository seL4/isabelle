(*  Title:      HOL/Induct/Common_Patterns.thy
    Author:     Makarius
*)

section \<open>Common patterns of induction\<close>

theory Common_Patterns
imports Main
begin

text \<open>
  The subsequent Isar proof schemes illustrate common proof patterns
  supported by the generic \<open>induct\<close> method.

  To demonstrate variations on statement (goal) structure we refer to
  the induction rule of Peano natural numbers: @{thm nat.induct
  [no_vars]}, which is the simplest case of datatype induction.  We
  shall also see more complex (mutual) datatype inductions involving
  several rules.  Working with inductive predicates is similar, but
  involves explicit facts about membership, instead of implicit
  syntactic typing.
\<close>


subsection \<open>Variations on statement structure\<close>

subsubsection \<open>Local facts and parameters\<close>

text \<open>
  Augmenting a problem by additional facts and locally fixed variables
  is a bread-and-butter method in many applications.  This is where
  unwieldy object-level \<open>\<forall>\<close> and \<open>\<longrightarrow>\<close> used to occur in
  the past.  The \<open>induct\<close> method works with primary means of
  the proof language instead.
\<close>

lemma
  fixes n :: nat
    and x :: 'a
  assumes "A n x"
  shows "P n x" using \<open>A n x\<close>
proof (induct n arbitrary: x)
  case 0
  note prem = \<open>A 0 x\<close>
  show "P 0 x" \<proof>
next
  case (Suc n)
  note hyp = \<open>\<And>x. A n x \<Longrightarrow> P n x\<close>
    and prem = \<open>A (Suc n) x\<close>
  show "P (Suc n) x" \<proof>
qed


subsubsection \<open>Local definitions\<close>

text \<open>
  Here the idea is to turn sub-expressions of the problem into a
  defined induction variable.  This is often accompanied with fixing
  of auxiliary parameters in the original expression, otherwise the
  induction step would refer invariably to particular entities.  This
  combination essentially expresses a partially abstracted
  representation of inductive expressions.
\<close>

lemma
  fixes a :: "'a \<Rightarrow> nat"
  assumes "A (a x)"
  shows "P (a x)" using \<open>A (a x)\<close>
proof (induct n \<equiv> "a x" arbitrary: x)
  case 0
  note prem = \<open>A (a x)\<close>
    and defn = \<open>0 = a x\<close>
  show "P (a x)" \<proof>
next
  case (Suc n)
  note hyp = \<open>\<And>x. n = a x \<Longrightarrow> A (a x) \<Longrightarrow> P (a x)\<close>
    and prem = \<open>A (a x)\<close>
    and defn = \<open>Suc n = a x\<close>
  show "P (a x)" \<proof>
qed

text \<open>
  Observe how the local definition \<open>n = a x\<close> recurs in the
  inductive cases as \<open>0 = a x\<close> and \<open>Suc n = a x\<close>,
  according to underlying induction rule.
\<close>


subsubsection \<open>Simple simultaneous goals\<close>

text \<open>
  The most basic simultaneous induction operates on several goals
  one-by-one, where each case refers to induction hypotheses that are
  duplicated according to the number of conclusions.
\<close>

lemma
  fixes n :: nat
  shows "P n" and "Q n"
proof (induct n)
  case 0 case 1
  show "P 0" \<proof>
next
  case 0 case 2
  show "Q 0" \<proof>
next
  case (Suc n) case 1
  note hyps = \<open>P n\<close> \<open>Q n\<close>
  show "P (Suc n)" \<proof>
next
  case (Suc n) case 2
  note hyps = \<open>P n\<close> \<open>Q n\<close>
  show "Q (Suc n)" \<proof>
qed

text \<open>
  The split into subcases may be deferred as follows -- this is
  particularly relevant for goal statements with local premises.
\<close>

lemma
  fixes n :: nat
  shows "A n \<Longrightarrow> P n"
    and "B n \<Longrightarrow> Q n"
proof (induct n)
  case 0
  {
    case 1
    note \<open>A 0\<close>
    show "P 0" \<proof>
  next
    case 2
    note \<open>B 0\<close>
    show "Q 0" \<proof>
  }
next
  case (Suc n)
  note \<open>A n \<Longrightarrow> P n\<close>
    and \<open>B n \<Longrightarrow> Q n\<close>
  {
    case 1
    note \<open>A (Suc n)\<close>
    show "P (Suc n)" \<proof>
  next
    case 2
    note \<open>B (Suc n)\<close>
    show "Q (Suc n)" \<proof>
  }
qed


subsubsection \<open>Compound simultaneous goals\<close>

text \<open>
  The following pattern illustrates the slightly more complex
  situation of simultaneous goals with individual local assumptions.
  In compound simultaneous statements like this, local assumptions
  need to be included into each goal, using \<open>\<Longrightarrow>\<close> of the Pure
  framework.  In contrast, local parameters do not require separate
  \<open>\<And>\<close> prefixes here, but may be moved into the common context
  of the whole statement.
\<close>

lemma
  fixes n :: nat
    and x :: 'a
    and y :: 'b
  shows "A n x \<Longrightarrow> P n x"
    and "B n y \<Longrightarrow> Q n y"
proof (induct n arbitrary: x y)
  case 0
  {
    case 1
    note prem = \<open>A 0 x\<close>
    show "P 0 x" \<proof>
  }
  {
    case 2
    note prem = \<open>B 0 y\<close>
    show "Q 0 y" \<proof>
  }
next
  case (Suc n)
  note hyps = \<open>\<And>x. A n x \<Longrightarrow> P n x\<close> \<open>\<And>y. B n y \<Longrightarrow> Q n y\<close>
  then have some_intermediate_result \<proof>
  {
    case 1
    note prem = \<open>A (Suc n) x\<close>
    show "P (Suc n) x" \<proof>
  }
  {
    case 2
    note prem = \<open>B (Suc n) y\<close>
    show "Q (Suc n) y" \<proof>
  }
qed

text \<open>
  Here \<open>induct\<close> provides again nested cases with numbered
  sub-cases, which allows to share common parts of the body context.
  In typical applications, there could be a long intermediate proof of
  general consequences of the induction hypotheses, before finishing
  each conclusion separately.
\<close>


subsection \<open>Multiple rules\<close>

text \<open>
  Multiple induction rules emerge from mutual definitions of
  datatypes, inductive predicates, functions etc.  The \<open>induct\<close> method accepts replicated arguments (with \<open>and\<close>
  separator), corresponding to each projection of the induction
  principle.

  The goal statement essentially follows the same arrangement,
  although it might be subdivided into simultaneous sub-problems as
  before!
\<close>

datatype foo = Foo1 nat | Foo2 bar
  and bar = Bar1 bool | Bar2 bazar
  and bazar = Bazar foo

text \<open>
  The pack of induction rules for this datatype is: @{thm [display]
  foo.induct [no_vars] bar.induct [no_vars] bazar.induct [no_vars]}

  This corresponds to the following basic proof pattern:
\<close>

lemma
  fixes foo :: foo
    and bar :: bar
    and bazar :: bazar
  shows "P foo"
    and "Q bar"
    and "R bazar"
proof (induct foo and bar and bazar)
  case (Foo1 n)
  show "P (Foo1 n)" \<proof>
next
  case (Foo2 bar)
  note \<open>Q bar\<close>
  show "P (Foo2 bar)" \<proof>
next
  case (Bar1 b)
  show "Q (Bar1 b)" \<proof>
next
  case (Bar2 bazar)
  note \<open>R bazar\<close>
  show "Q (Bar2 bazar)" \<proof>
next
  case (Bazar foo)
  note \<open>P foo\<close>
  show "R (Bazar foo)" \<proof>
qed

text \<open>
  This can be combined with the previous techniques for compound
  statements, e.g.\ like this.
\<close>

lemma
  fixes x :: 'a and y :: 'b and z :: 'c
    and foo :: foo
    and bar :: bar
    and bazar :: bazar
  shows
    "A x foo \<Longrightarrow> P x foo"
  and
    "B1 y bar \<Longrightarrow> Q1 y bar"
    "B2 y bar \<Longrightarrow> Q2 y bar"
  and
    "C1 z bazar \<Longrightarrow> R1 z bazar"
    "C2 z bazar \<Longrightarrow> R2 z bazar"
    "C3 z bazar \<Longrightarrow> R3 z bazar"
proof (induct foo and bar and bazar arbitrary: x and y and z)
  oops


subsection \<open>Inductive predicates\<close>

text \<open>
  The most basic form of induction involving predicates (or sets)
  essentially eliminates a given membership fact.
\<close>

inductive Even :: "nat \<Rightarrow> bool" where
  zero: "Even 0"
| double: "Even (2 * n)" if "Even n" for n

lemma
  assumes "Even n"
  shows "P n"
  using assms
proof induct
  case zero
  show "P 0" \<proof>
next
  case (double n)
  note \<open>Even n\<close> and \<open>P n\<close>
  show "P (2 * n)" \<proof>
qed

text \<open>
  Alternatively, an initial rule statement may be proven as follows,
  performing ``in-situ'' elimination with explicit rule specification.
\<close>

lemma "Even n \<Longrightarrow> P n"
proof (induct rule: Even.induct)
  oops

text \<open>
  Simultaneous goals do not introduce anything new.
\<close>

lemma
  assumes "Even n"
  shows "P1 n" and "P2 n"
  using assms
proof induct
  case zero
  {
    case 1
    show "P1 0" \<proof>
  next
    case 2
    show "P2 0" \<proof>
  }
next
  case (double n)
  note \<open>Even n\<close> and \<open>P1 n\<close> and \<open>P2 n\<close>
  {
    case 1
    show "P1 (2 * n)" \<proof>
  next
    case 2
    show "P2 (2 * n)" \<proof>
  }
qed

text \<open>
  Working with mutual rules requires special care in composing the
  statement as a two-level conjunction, using lists of propositions
  separated by \<open>and\<close>.  For example:
\<close>

inductive Evn :: "nat \<Rightarrow> bool" and Odd :: "nat \<Rightarrow> bool"
where
  zero: "Evn 0"
| succ_Evn: "Odd (Suc n)" if "Evn n" for n
| succ_Odd: "Evn (Suc n)" if "Odd n" for n

lemma
    "Evn n \<Longrightarrow> P1 n"
    "Evn n \<Longrightarrow> P2 n"
    "Evn n \<Longrightarrow> P3 n"
  and
    "Odd n \<Longrightarrow> Q1 n"
    "Odd n \<Longrightarrow> Q2 n"
proof (induct rule: Evn_Odd.inducts)
  case zero
  { case 1 show "P1 0" \<proof> }
  { case 2 show "P2 0" \<proof> }
  { case 3 show "P3 0" \<proof> }
next
  case (succ_Evn n)
  note \<open>Evn n\<close> and \<open>P1 n\<close> \<open>P2 n\<close> \<open>P3 n\<close>
  { case 1 show "Q1 (Suc n)" \<proof> }
  { case 2 show "Q2 (Suc n)" \<proof> }
next
  case (succ_Odd n)
  note \<open>Odd n\<close> and \<open>Q1 n\<close> \<open>Q2 n\<close>
  { case 1 show "P1 (Suc n)" \<proof> }
  { case 2 show "P2 (Suc n)" \<proof> }
  { case 3 show "P3 (Suc n)" \<proof> }
qed


text \<open>
  Cases and hypotheses in each case can be named explicitly.
\<close>

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r
where
  refl: "star r x x" for x
| step: "star r x z" if "r x y" and "star r y z" for x y z

text \<open>Underscores are replaced by the default name hyps:\<close>

lemmas star_induct = star.induct [case_names base step[r _ IH]]

lemma "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof (induct rule: star_induct) print_cases
  case base
  then show ?case .
next
  case (step a b c) print_facts
  from step.prems have "star r b z" by (rule step.IH)
  with step.r show ?case by (rule star.step)
qed

end
