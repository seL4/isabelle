(*  Title:      HOL/Induct/Common_Patterns.thy
    Author:     Makarius
*)

header {* Common patterns of induction *}

theory Common_Patterns
imports Main
begin

text {*
  The subsequent Isar proof schemes illustrate common proof patterns
  supported by the generic @{text "induct"} method.

  To demonstrate variations on statement (goal) structure we refer to
  the induction rule of Peano natural numbers: @{thm nat.induct
  [no_vars]}, which is the simplest case of datatype induction.  We
  shall also see more complex (mutual) datatype inductions involving
  several rules.  Working with inductive predicates is similar, but
  involves explicit facts about membership, instead of implicit
  syntactic typing.
*}


subsection {* Variations on statement structure *}

subsubsection {* Local facts and parameters *}

text {*
  Augmenting a problem by additional facts and locally fixed variables
  is a bread-and-butter method in many applications.  This is where
  unwieldy object-level @{text "\<forall>"} and @{text "\<longrightarrow>"} used to occur in
  the past.  The @{text "induct"} method works with primary means of
  the proof language instead.
*}

lemma
  fixes n :: nat
    and x :: 'a
  assumes "A n x"
  shows "P n x" using `A n x`
proof (induct n arbitrary: x)
  case 0
  note prem = `A 0 x`
  show "P 0 x" sorry
next
  case (Suc n)
  note hyp = `\<And>x. A n x \<Longrightarrow> P n x`
    and prem = `A (Suc n) x`
  show "P (Suc n) x" sorry
qed


subsubsection {* Local definitions *}

text {*
  Here the idea is to turn sub-expressions of the problem into a
  defined induction variable.  This is often accompanied with fixing
  of auxiliary parameters in the original expression, otherwise the
  induction step would refer invariably to particular entities.  This
  combination essentially expresses a partially abstracted
  representation of inductive expressions.
*}

lemma
  fixes a :: "'a \<Rightarrow> nat"
  assumes "A (a x)"
  shows "P (a x)" using `A (a x)`
proof (induct n \<equiv> "a x" arbitrary: x)
  case 0
  note prem = `A (a x)`
    and defn = `0 = a x`
  show "P (a x)" sorry
next
  case (Suc n)
  note hyp = `\<And>x. A (a x) \<Longrightarrow> n = a x \<Longrightarrow> P (a x)`
    and prem = `A (a x)`
    and defn = `Suc n = a x`
  show "P (a x)" sorry
qed

text {*
  Observe how the local definition @{text "n = a x"} recurs in the
  inductive cases as @{text "0 = a x"} and @{text "Suc n = a x"},
  according to underlying induction rule.
*}


subsubsection {* Simple simultaneous goals *}

text {*
  The most basic simultaneous induction operates on several goals
  one-by-one, where each case refers to induction hypotheses that are
  duplicated according to the number of conclusions.
*}

lemma
  fixes n :: nat
  shows "P n" and "Q n"
proof (induct n)
  case 0 case 1
  show "P 0" sorry
next
  case 0 case 2
  show "Q 0" sorry
next
  case (Suc n) case 1
  note hyps = `P n` `Q n`
  show "P (Suc n)" sorry
next
  case (Suc n) case 2
  note hyps = `P n` `Q n`
  show "Q (Suc n)" sorry
qed

text {*
  The split into subcases may be deferred as follows -- this is
  particularly relevant for goal statements with local premises.
*}

lemma
  fixes n :: nat
  shows "A n \<Longrightarrow> P n"
    and "B n \<Longrightarrow> Q n"
proof (induct n)
  case 0
  {
    case 1
    note `A 0`
    show "P 0" sorry
  next
    case 2
    note `B 0`
    show "Q 0" sorry
  }
next
  case (Suc n)
  note `A n \<Longrightarrow> P n`
    and `B n \<Longrightarrow> Q n`
  {
    case 1
    note `A (Suc n)`
    show "P (Suc n)" sorry
  next
    case 2
    note `B (Suc n)`
    show "Q (Suc n)" sorry
  }
qed


subsubsection {* Compound simultaneous goals *}

text {*
  The following pattern illustrates the slightly more complex
  situation of simultaneous goals with individual local assumptions.
  In compound simultaneous statements like this, local assumptions
  need to be included into each goal, using @{text "\<Longrightarrow>"} of the Pure
  framework.  In contrast, local parameters do not require separate
  @{text "\<And>"} prefixes here, but may be moved into the common context
  of the whole statement.
*}

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
    note prem = `A 0 x`
    show "P 0 x" sorry
  }
  {
    case 2
    note prem = `B 0 y`
    show "Q 0 y" sorry
  }
next
  case (Suc n)
  note hyps = `\<And>x. A n x \<Longrightarrow> P n x` `\<And>y. B n y \<Longrightarrow> Q n y`
  then have some_intermediate_result sorry
  {
    case 1
    note prem = `A (Suc n) x`
    show "P (Suc n) x" sorry
  }
  {
    case 2
    note prem = `B (Suc n) y`
    show "Q (Suc n) y" sorry
  }
qed

text {*
  Here @{text "induct"} provides again nested cases with numbered
  sub-cases, which allows to share common parts of the body context.
  In typical applications, there could be a long intermediate proof of
  general consequences of the induction hypotheses, before finishing
  each conclusion separately.
*}


subsection {* Multiple rules *}

text {*
  Multiple induction rules emerge from mutual definitions of
  datatypes, inductive predicates, functions etc.  The @{text
  "induct"} method accepts replicated arguments (with @{text "and"}
  separator), corresponding to each projection of the induction
  principle.

  The goal statement essentially follows the same arrangement,
  although it might be subdivided into simultaneous sub-problems as
  before!
*}

datatype foo = Foo1 nat | Foo2 bar
  and bar = Bar1 bool | Bar2 bazar
  and bazar = Bazar foo

text {*
  The pack of induction rules for this datatype is: @{thm [display]
  foo_bar_bazar.inducts [no_vars]}

  This corresponds to the following basic proof pattern:
*}

lemma
  fixes foo :: foo
    and bar :: bar
    and bazar :: bazar
  shows "P foo"
    and "Q bar"
    and "R bazar"
proof (induct foo and bar and bazar)
  case (Foo1 n)
  show "P (Foo1 n)" sorry
next
  case (Foo2 bar)
  note `Q bar`
  show "P (Foo2 bar)" sorry
next
  case (Bar1 b)
  show "Q (Bar1 b)" sorry
next
  case (Bar2 bazar)
  note `R bazar`
  show "Q (Bar2 bazar)" sorry
next
  case (Bazar foo)
  note `P foo`
  show "R (Bazar foo)" sorry
qed

text {*
  This can be combined with the previous techniques for compound
  statements, e.g.\ like this.
*}

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


subsection {* Inductive predicates *}

text {*
  The most basic form of induction involving predicates (or sets)
  essentially eliminates a given membership fact.
*}

inductive Even :: "nat \<Rightarrow> bool" where
  zero: "Even 0"
| double: "Even n \<Longrightarrow> Even (2 * n)"

lemma
  assumes "Even n"
  shows "P n"
  using assms
proof induct
  case zero
  show "P 0" sorry
next
  case (double n)
  note `Even n` and `P n`
  show "P (2 * n)" sorry
qed

text {*
  Alternatively, an initial rule statement may be proven as follows,
  performing ``in-situ'' elimination with explicit rule specification.
*}

lemma "Even n \<Longrightarrow> P n"
proof (induct rule: Even.induct)
  oops

text {*
  Simultaneous goals do not introduce anything new.
*}

lemma
  assumes "Even n"
  shows "P1 n" and "P2 n"
  using assms
proof induct
  case zero
  {
    case 1
    show "P1 0" sorry
  next
    case 2
    show "P2 0" sorry
  }
next
  case (double n)
  note `Even n` and `P1 n` and `P2 n`
  {
    case 1
    show "P1 (2 * n)" sorry
  next
    case 2
    show "P2 (2 * n)" sorry
  }
qed

text {*
  Working with mutual rules requires special care in composing the
  statement as a two-level conjunction, using lists of propositions
  separated by @{text "and"}.  For example:
*}

inductive Evn :: "nat \<Rightarrow> bool" and Odd :: "nat \<Rightarrow> bool"
where
  zero: "Evn 0"
| succ_Evn: "Evn n \<Longrightarrow> Odd (Suc n)"
| succ_Odd: "Odd n \<Longrightarrow> Evn (Suc n)"

lemma
    "Evn n \<Longrightarrow> P1 n"
    "Evn n \<Longrightarrow> P2 n"
    "Evn n \<Longrightarrow> P3 n"
  and
    "Odd n \<Longrightarrow> Q1 n"
    "Odd n \<Longrightarrow> Q2 n"
proof (induct rule: Evn_Odd.inducts)
  case zero
  { case 1 show "P1 0" sorry }
  { case 2 show "P2 0" sorry }
  { case 3 show "P3 0" sorry }
next
  case (succ_Evn n)
  note `Evn n` and `P1 n` `P2 n` `P3 n`
  { case 1 show "Q1 (Suc n)" sorry }
  { case 2 show "Q2 (Suc n)" sorry }
next
  case (succ_Odd n)
  note `Odd n` and `Q1 n` `Q2 n`
  { case 1 show "P1 (Suc n)" sorry }
  { case 2 show "P2 (Suc n)" sorry }
  { case 3 show "P3 (Suc n)" sorry }
qed

end