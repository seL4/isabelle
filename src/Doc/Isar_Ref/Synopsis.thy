(*:maxLineLen=78:*)

theory Synopsis
  imports Main Base
begin

chapter \<open>Synopsis\<close>

section \<open>Notepad\<close>

text \<open>
  An Isar proof body serves as mathematical notepad to compose logical
  content, consisting of types, terms, facts.
\<close>


subsection \<open>Types and terms\<close>

notepad
begin
  txt \<open>Locally fixed entities:\<close>
  fix x   \<comment> \<open>local constant, without any type information yet\<close>
  fix x :: 'a  \<comment> \<open>variant with explicit type-constraint for subsequent use\<close>

  fix a b
  assume "a = b"  \<comment> \<open>type assignment at first occurrence in concrete term\<close>

  txt \<open>Definitions (non-polymorphic):\<close>
  define x :: 'a where "x = t"

  txt \<open>Abbreviations (polymorphic):\<close>
  let ?f = "\<lambda>x. x"
  term "?f ?f"

  txt \<open>Notation:\<close>
  write x  (\<open>***\<close>)
end


subsection \<open>Facts\<close>

text \<open>
  A fact is a simultaneous list of theorems.
\<close>


subsubsection \<open>Producing facts\<close>

notepad
begin

  txt \<open>Via assumption (``lambda''):\<close>
  assume a: A

  txt \<open>Via proof (``let''):\<close>
  have b: B \<proof>

  txt \<open>Via abbreviation (``let''):\<close>
  note c = a b

end


subsubsection \<open>Referencing facts\<close>

notepad
begin
  txt \<open>Via explicit name:\<close>
  assume a: A
  note a

  txt \<open>Via implicit name:\<close>
  assume A
  note this

  txt \<open>Via literal proposition (unification with results from the proof text):\<close>
  assume A
  note \<open>A\<close>

  assume "\<And>x. B x"
  note \<open>B a\<close>
  note \<open>B b\<close>
end


subsubsection \<open>Manipulating facts\<close>

notepad
begin
  txt \<open>Instantiation:\<close>
  assume a: "\<And>x. B x"
  note a
  note a [of b]
  note a [where x = b]

  txt \<open>Backchaining:\<close>
  assume 1: A
  assume 2: "A \<Longrightarrow> C"
  note 2 [OF 1]
  note 1 [THEN 2]

  txt \<open>Symmetric results:\<close>
  assume "x = y"
  note this [symmetric]

  assume "x \<noteq> y"
  note this [symmetric]

  txt \<open>Adhoc-simplification (take care!):\<close>
  assume "P ([] @ xs)"
  note this [simplified]
end


subsubsection \<open>Projections\<close>

text \<open>
  Isar facts consist of multiple theorems.  There is notation to project
  interval ranges.
\<close>

notepad
begin
  assume stuff: A B C D
  note stuff(1)
  note stuff(2-3)
  note stuff(2-)
end


subsubsection \<open>Naming conventions\<close>

text \<open>
  \<^item> Lower-case identifiers are usually preferred.

  \<^item> Facts can be named after the main term within the proposition.

  \<^item> Facts should \<^emph>\<open>not\<close> be named after the command that
  introduced them (@{command "assume"}, @{command "have"}).  This is
  misleading and hard to maintain.

  \<^item> Natural numbers can be used as ``meaningless'' names (more
  appropriate than \<open>a1\<close>, \<open>a2\<close> etc.)

  \<^item> Symbolic identifiers are supported (e.g. \<open>*\<close>, \<open>**\<close>, \<open>***\<close>).
\<close>


subsection \<open>Block structure\<close>

text \<open>
  The formal notepad is block structured.  The fact produced by the last
  entry of a block is exported into the outer context.
\<close>

notepad
begin
  {
    have a: A \<proof>
    have b: B \<proof>
    note a b
  }
  note this
  note \<open>A\<close>
  note \<open>B\<close>
end

text \<open>Explicit blocks as well as implicit blocks of nested goal
  statements (e.g.\ @{command have}) automatically introduce one extra
  pair of parentheses in reserve.  The @{command next} command allows
  to ``jump'' between these sub-blocks.\<close>

notepad
begin

  {
    have a: A \<proof>
  next
    have b: B
    proof -
      show B \<proof>
    next
      have c: C \<proof>
    next
      have d: D \<proof>
    qed
  }

  txt \<open>Alternative version with explicit parentheses everywhere:\<close>

  {
    {
      have a: A \<proof>
    }
    {
      have b: B
      proof -
        {
          show B \<proof>
        }
        {
          have c: C \<proof>
        }
        {
          have d: D \<proof>
        }
      qed
    }
  }

end


section \<open>Calculational reasoning \label{sec:calculations-synopsis}\<close>

text \<open>
  For example, see \<^file>\<open>~~/src/HOL/Isar_Examples/Group.thy\<close>.
\<close>


subsection \<open>Special names in Isar proofs\<close>

text \<open>
  \<^item> term \<open>?thesis\<close> --- the main conclusion of the
  innermost pending claim

  \<^item> term \<open>\<dots>\<close> --- the argument of the last explicitly
  stated result (for infix application this is the right-hand side)

  \<^item> fact \<open>this\<close> --- the last result produced in the text
\<close>

notepad
begin
  have "x = y"
  proof -
    term ?thesis
    show ?thesis \<proof>
    term ?thesis  \<comment> \<open>static!\<close>
  qed
  term "\<dots>"
  thm this
end

text \<open>Calculational reasoning maintains the special fact called
  ``\<open>calculation\<close>'' in the background.  Certain language
  elements combine primary \<open>this\<close> with secondary \<open>calculation\<close>.\<close>


subsection \<open>Transitive chains\<close>

text \<open>The Idea is to combine \<open>this\<close> and \<open>calculation\<close>
  via typical \<open>trans\<close> rules (see also @{command
  print_trans_rules}):\<close>

thm trans
thm less_trans
thm less_le_trans

notepad
begin
  txt \<open>Plain bottom-up calculation:\<close>
  have "a = b" \<proof>
  also
  have "b = c" \<proof>
  also
  have "c = d" \<proof>
  finally
  have "a = d" .

  txt \<open>Variant using the \<open>\<dots>\<close> abbreviation:\<close>
  have "a = b" \<proof>
  also
  have "\<dots> = c" \<proof>
  also
  have "\<dots> = d" \<proof>
  finally
  have "a = d" .

  txt \<open>Top-down version with explicit claim at the head:\<close>
  have "a = d"
  proof -
    have "a = b" \<proof>
    also
    have "\<dots> = c" \<proof>
    also
    have "\<dots> = d" \<proof>
    finally
    show ?thesis .
  qed
next
  txt \<open>Mixed inequalities (require suitable base type):\<close>
  fix a b c d :: nat

  have "a < b" \<proof>
  also
  have "b \<le> c" \<proof>
  also
  have "c = d" \<proof>
  finally
  have "a < d" .
end


subsubsection \<open>Notes\<close>

text \<open>
  \<^item> The notion of \<open>trans\<close> rule is very general due to the
  flexibility of Isabelle/Pure rule composition.

  \<^item> User applications may declare their own rules, with some care
  about the operational details of higher-order unification.
\<close>


subsection \<open>Degenerate calculations\<close>

text \<open>The Idea is to append \<open>this\<close> to \<open>calculation\<close>, without rule composition.
  This is occasionally useful to avoid naming intermediate facts.\<close>

notepad
begin
  txt \<open>A vacuous proof:\<close>
  have A \<proof>
  moreover
  have B \<proof>
  moreover
  have C \<proof>
  ultimately
  have A and B and C .
next
  txt \<open>Slightly more content (trivial bigstep reasoning):\<close>
  have A \<proof>
  moreover
  have B \<proof>
  moreover
  have C \<proof>
  ultimately
  have "A \<and> B \<and> C" by blast
end

text \<open>Note that For multi-branch case splitting, it is better to use @{command
  consider}.\<close>


section \<open>Induction\<close>

subsection \<open>Induction as Natural Deduction\<close>

text \<open>In principle, induction is just a special case of Natural
  Deduction (see also \secref{sec:natural-deduction-synopsis}).  For
  example:\<close>

thm nat.induct
print_statement nat.induct

notepad
begin
  fix n :: nat
  have "P n"
  proof (rule nat.induct)  \<comment> \<open>fragile rule application!\<close>
    show "P 0" \<proof>
  next
    fix n :: nat
    assume "P n"
    show "P (Suc n)" \<proof>
  qed
end

text \<open>
  In practice, much more proof infrastructure is required.

  The proof method @{method induct} provides:

  \<^item> implicit rule selection and robust instantiation

  \<^item> context elements via symbolic case names

  \<^item> support for rule-structured induction statements, with local
  parameters, premises, etc.
\<close>

notepad
begin
  fix n :: nat
  have "P n"
  proof (induct n)
    case 0
    show ?case \<proof>
  next
    case (Suc n)
    from Suc.hyps show ?case \<proof>
  qed
end


subsubsection \<open>Example\<close>

text \<open>
  The subsequent example combines the following proof patterns:

  \<^item> outermost induction (over the datatype structure of natural
  numbers), to decompose the proof problem in top-down manner

  \<^item> calculational reasoning (\secref{sec:calculations-synopsis})
  to compose the result in each case

  \<^item> solving local claims within the calculation by simplification
\<close>

lemma
  fixes n :: nat
  shows "(\<Sum>i=0..n. i) = n * (n + 1) div 2"
proof (induct n)
  case 0
  have "(\<Sum>i=0..0. i) = (0::nat)" by simp
  also have "\<dots> = 0 * (0 + 1) div 2" by simp
  finally show ?case .
next
  case (Suc n)
  have "(\<Sum>i=0..Suc n. i) = (\<Sum>i=0..n. i) + (n + 1)" by simp
  also have "\<dots> = n * (n + 1) div 2 + (n + 1)" by (simp add: Suc.hyps)
  also have "\<dots> = (n * (n + 1) + 2 * (n + 1)) div 2" by simp
  also have "\<dots> = (Suc n * (Suc n + 1)) div 2" by simp
  finally show ?case .
qed

text \<open>This demonstrates how induction proofs can be done without
  having to consider the raw Natural Deduction structure.\<close>


subsection \<open>Induction with local parameters and premises\<close>

text \<open>Idea: Pure rule statements are passed through the induction
  rule.  This achieves convenient proof patterns, thanks to some
  internal trickery in the @{method induct} method.

  Important: Using compact HOL formulae with \<open>\<forall>/\<longrightarrow>\<close> is a
  well-known anti-pattern! It would produce useless formal noise.
\<close>

notepad
begin
  fix n :: nat
  fix P :: "nat \<Rightarrow> bool"
  fix Q :: "'a \<Rightarrow> nat \<Rightarrow> bool"

  have "P n"
  proof (induct n)
    case 0
    show "P 0" \<proof>
  next
    case (Suc n)
    from \<open>P n\<close> show "P (Suc n)" \<proof>
  qed

  have "A n \<Longrightarrow> P n"
  proof (induct n)
    case 0
    from \<open>A 0\<close> show "P 0" \<proof>
  next
    case (Suc n)
    from \<open>A n \<Longrightarrow> P n\<close>
      and \<open>A (Suc n)\<close> show "P (Suc n)" \<proof>
  qed

  have "\<And>x. Q x n"
  proof (induct n)
    case 0
    show "Q x 0" \<proof>
  next
    case (Suc n)
    from \<open>\<And>x. Q x n\<close> show "Q x (Suc n)" \<proof>
    txt \<open>Local quantification admits arbitrary instances:\<close>
    note \<open>Q a n\<close> and \<open>Q b n\<close>
  qed
end


subsection \<open>Implicit induction context\<close>

text \<open>The @{method induct} method can isolate local parameters and
  premises directly from the given statement.  This is convenient in
  practical applications, but requires some understanding of what is
  going on internally (as explained above).\<close>

notepad
begin
  fix n :: nat
  fix Q :: "'a \<Rightarrow> nat \<Rightarrow> bool"

  fix x :: 'a
  assume "A x n"
  then have "Q x n"
  proof (induct n arbitrary: x)
    case 0
    from \<open>A x 0\<close> show "Q x 0" \<proof>
  next
    case (Suc n)
    from \<open>\<And>x. A x n \<Longrightarrow> Q x n\<close>  \<comment> \<open>arbitrary instances can be produced here\<close>
      and \<open>A x (Suc n)\<close> show "Q x (Suc n)" \<proof>
  qed
end


subsection \<open>Advanced induction with term definitions\<close>

text \<open>Induction over subexpressions of a certain shape are delicate
  to formalize.  The Isar @{method induct} method provides
  infrastructure for this.

  Idea: sub-expressions of the problem are turned into a defined
  induction variable; often accompanied with fixing of auxiliary
  parameters in the original expression.\<close>

notepad
begin
  fix a :: "'a \<Rightarrow> nat"
  fix A :: "nat \<Rightarrow> bool"

  assume "A (a x)"
  then have "P (a x)"
  proof (induct "a x" arbitrary: x)
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
end


section \<open>Natural Deduction \label{sec:natural-deduction-synopsis}\<close>

subsection \<open>Rule statements\<close>

text \<open>
  Isabelle/Pure ``theorems'' are always natural deduction rules,
  which sometimes happen to consist of a conclusion only.

  The framework connectives \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> indicate the
  rule structure declaratively.  For example:\<close>

thm conjI
thm impI
thm nat.induct

text \<open>
  The object-logic is embedded into the Pure framework via an implicit
  derivability judgment \<^term>\<open>Trueprop :: bool \<Rightarrow> prop\<close>.

  Thus any HOL formulae appears atomic to the Pure framework, while
  the rule structure outlines the corresponding proof pattern.

  This can be made explicit as follows:
\<close>

notepad
begin
  write Trueprop  (\<open>Tr\<close>)

  thm conjI
  thm impI
  thm nat.induct
end

text \<open>
  Isar provides first-class notation for rule statements as follows.
\<close>

print_statement conjI
print_statement impI
print_statement nat.induct


subsubsection \<open>Examples\<close>

text \<open>
  Introductions and eliminations of some standard connectives of
  the object-logic can be written as rule statements as follows.  (The
  proof ``@{command "by"}~@{method blast}'' serves as sanity check.)
\<close>

lemma "(P \<Longrightarrow> False) \<Longrightarrow> \<not> P" by blast
lemma "\<not> P \<Longrightarrow> P \<Longrightarrow> Q" by blast

lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q" by blast
lemma "P \<and> Q \<Longrightarrow> (P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R" by blast

lemma "P \<Longrightarrow> P \<or> Q" by blast
lemma "Q \<Longrightarrow> P \<or> Q" by blast
lemma "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R" by blast

lemma "(\<And>x. P x) \<Longrightarrow> (\<forall>x. P x)" by blast
lemma "(\<forall>x. P x) \<Longrightarrow> P x" by blast

lemma "P x \<Longrightarrow> (\<exists>x. P x)" by blast
lemma "(\<exists>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> R) \<Longrightarrow> R" by blast

lemma "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A \<inter> B" by blast
lemma "x \<in> A \<inter> B \<Longrightarrow> (x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> R) \<Longrightarrow> R" by blast

lemma "x \<in> A \<Longrightarrow> x \<in> A \<union> B" by blast
lemma "x \<in> B \<Longrightarrow> x \<in> A \<union> B" by blast
lemma "x \<in> A \<union> B \<Longrightarrow> (x \<in> A \<Longrightarrow> R) \<Longrightarrow> (x \<in> B \<Longrightarrow> R) \<Longrightarrow> R" by blast


subsection \<open>Isar context elements\<close>

text \<open>We derive some results out of the blue, using Isar context
  elements and some explicit blocks.  This illustrates their meaning
  wrt.\ Pure connectives, without goal states getting in the way.\<close>

notepad
begin
  {
    fix x
    have "B x" \<proof>
  }
  have "\<And>x. B x" by fact

next

  {
    assume A
    have B \<proof>
  }
  have "A \<Longrightarrow> B" by fact

next

  {
    define x where "x = t"
    have "B x" \<proof>
  }
  have "B t" by fact

next

  {
    obtain x :: 'a where "B x" \<proof>
    have C \<proof>
  }
  have C by fact

end


subsection \<open>Pure rule composition\<close>

text \<open>
  The Pure framework provides means for:

  \<^item> backward-chaining of rules by @{inference resolution}

  \<^item> closing of branches by @{inference assumption}


  Both principles involve higher-order unification of \<open>\<lambda>\<close>-terms
  modulo \<open>\<alpha>\<beta>\<eta>\<close>-equivalence (cf.\ Huet and Miller).
\<close>

notepad
begin
  assume a: A and b: B
  thm conjI
  thm conjI [of A B]  \<comment> \<open>instantiation\<close>
  thm conjI [of A B, OF a b]  \<comment> \<open>instantiation and composition\<close>
  thm conjI [OF a b]  \<comment> \<open>composition via unification (trivial)\<close>
  thm conjI [OF \<open>A\<close> \<open>B\<close>]

  thm conjI [OF disjI1]
end

text \<open>Note: Low-level rule composition is tedious and leads to
  unreadable~/ unmaintainable expressions in the text.\<close>


subsection \<open>Structured backward reasoning\<close>

text \<open>Idea: Canonical proof decomposition via @{command fix}~/
  @{command assume}~/ @{command show}, where the body produces a
  natural deduction rule to refine some goal.\<close>

notepad
begin
  fix A B :: "'a \<Rightarrow> bool"

  have "\<And>x. A x \<Longrightarrow> B x"
  proof -
    fix x
    assume "A x"
    show "B x" \<proof>
  qed

  have "\<And>x. A x \<Longrightarrow> B x"
  proof -
    {
      fix x
      assume "A x"
      show "B x" \<proof>
    } \<comment> \<open>implicit block structure made explicit\<close>
    note \<open>\<And>x. A x \<Longrightarrow> B x\<close>
      \<comment> \<open>side exit for the resulting rule\<close>
  qed
end


subsection \<open>Structured rule application\<close>

text \<open>
  Idea: Previous facts and new claims are composed with a rule from
  the context (or background library).
\<close>

notepad
begin
  assume r\<^sub>1: "A \<Longrightarrow> B \<Longrightarrow> C"  \<comment> \<open>simple rule (Horn clause)\<close>

  have A \<proof>  \<comment> \<open>prefix of facts via outer sub-proof\<close>
  then have C
  proof (rule r\<^sub>1)
    show B \<proof>  \<comment> \<open>remaining rule premises via inner sub-proof\<close>
  qed

  have C
  proof (rule r\<^sub>1)
    show A \<proof>
    show B \<proof>
  qed

  have A and B \<proof>
  then have C
  proof (rule r\<^sub>1)
  qed

  have A and B \<proof>
  then have C by (rule r\<^sub>1)

next

  assume r\<^sub>2: "A \<Longrightarrow> (\<And>x. B\<^sub>1 x \<Longrightarrow> B\<^sub>2 x) \<Longrightarrow> C"  \<comment> \<open>nested rule\<close>

  have A \<proof>
  then have C
  proof (rule r\<^sub>2)
    fix x
    assume "B\<^sub>1 x"
    show "B\<^sub>2 x" \<proof>
  qed

  txt \<open>The compound rule premise \<^prop>\<open>\<And>x. B\<^sub>1 x \<Longrightarrow> B\<^sub>2 x\<close> is better
    addressed via @{command fix}~/ @{command assume}~/ @{command show}
    in the nested proof body.\<close>
end


subsection \<open>Example: predicate logic\<close>

text \<open>
  Using the above principles, standard introduction and elimination proofs
  of predicate logic connectives of HOL work as follows.
\<close>

notepad
begin
  have "A \<longrightarrow> B" and A \<proof>
  then have B ..

  have A \<proof>
  then have "A \<or> B" ..

  have B \<proof>
  then have "A \<or> B" ..

  have "A \<or> B" \<proof>
  then have C
  proof
    assume A
    then show C \<proof>
  next
    assume B
    then show C \<proof>
  qed

  have A and B \<proof>
  then have "A \<and> B" ..

  have "A \<and> B" \<proof>
  then have A ..

  have "A \<and> B" \<proof>
  then have B ..

  have False \<proof>
  then have A ..

  have True ..

  have "\<not> A"
  proof
    assume A
    then show False \<proof>
  qed

  have "\<not> A" and A \<proof>
  then have B ..

  have "\<forall>x. P x"
  proof
    fix x
    show "P x" \<proof>
  qed

  have "\<forall>x. P x" \<proof>
  then have "P a" ..

  have "\<exists>x. P x"
  proof
    show "P a" \<proof>
  qed

  have "\<exists>x. P x" \<proof>
  then have C
  proof
    fix a
    assume "P a"
    show C \<proof>
  qed

  txt \<open>Less awkward version using @{command obtain}:\<close>
  have "\<exists>x. P x" \<proof>
  then obtain a where "P a" ..
end

text \<open>Further variations to illustrate Isar sub-proofs involving
  @{command show}:\<close>

notepad
begin
  have "A \<and> B"
  proof  \<comment> \<open>two strictly isolated subproofs\<close>
    show A \<proof>
  next
    show B \<proof>
  qed

  have "A \<and> B"
  proof  \<comment> \<open>one simultaneous sub-proof\<close>
    show A and B \<proof>
  qed

  have "A \<and> B"
  proof  \<comment> \<open>two subproofs in the same context\<close>
    show A \<proof>
    show B \<proof>
  qed

  have "A \<and> B"
  proof  \<comment> \<open>swapped order\<close>
    show B \<proof>
    show A \<proof>
  qed

  have "A \<and> B"
  proof  \<comment> \<open>sequential subproofs\<close>
    show A \<proof>
    show B using \<open>A\<close> \<proof>
  qed
end


subsubsection \<open>Example: set-theoretic operators\<close>

text \<open>There is nothing special about logical connectives (\<open>\<and>\<close>, \<open>\<or>\<close>, \<open>\<forall>\<close>, \<open>\<exists>\<close> etc.).  Operators from
  set-theory or lattice-theory work analogously.  It is only a matter
  of rule declarations in the library; rules can be also specified
  explicitly.
\<close>

notepad
begin
  have "x \<in> A" and "x \<in> B" \<proof>
  then have "x \<in> A \<inter> B" ..

  have "x \<in> A" \<proof>
  then have "x \<in> A \<union> B" ..

  have "x \<in> B" \<proof>
  then have "x \<in> A \<union> B" ..

  have "x \<in> A \<union> B" \<proof>
  then have C
  proof
    assume "x \<in> A"
    then show C \<proof>
  next
    assume "x \<in> B"
    then show C \<proof>
  qed

next
  have "x \<in> \<Inter>A"
  proof
    fix a
    assume "a \<in> A"
    show "x \<in> a" \<proof>
  qed

  have "x \<in> \<Inter>A" \<proof>
  then have "x \<in> a"
  proof
    show "a \<in> A" \<proof>
  qed

  have "a \<in> A" and "x \<in> a" \<proof>
  then have "x \<in> \<Union>A" ..

  have "x \<in> \<Union>A" \<proof>
  then obtain a where "a \<in> A" and "x \<in> a" ..
end


section \<open>Generalized elimination and cases\<close>

subsection \<open>General elimination rules\<close>

text \<open>
  The general format of elimination rules is illustrated by the
  following typical representatives:
\<close>

thm exE     \<comment> \<open>local parameter\<close>
thm conjE   \<comment> \<open>local premises\<close>
thm disjE   \<comment> \<open>split into cases\<close>

text \<open>
  Combining these characteristics leads to the following general scheme
  for elimination rules with cases:

  \<^item> prefix of assumptions (or ``major premises'')

  \<^item> one or more cases that enable to establish the main conclusion
  in an augmented context
\<close>

notepad
begin
  assume r:
    "A\<^sub>1 \<Longrightarrow> A\<^sub>2 \<Longrightarrow>  \<comment> \<open>assumptions\<close>
      (\<And>x y. B\<^sub>1 x y \<Longrightarrow> C\<^sub>1 x y \<Longrightarrow> R) \<Longrightarrow>  \<comment> \<open>case 1\<close>
      (\<And>x y. B\<^sub>2 x y \<Longrightarrow> C\<^sub>2 x y \<Longrightarrow> R) \<Longrightarrow>  \<comment> \<open>case 2\<close>
      R  \<comment> \<open>main conclusion\<close>"

  have A\<^sub>1 and A\<^sub>2 \<proof>
  then have R
  proof (rule r)
    fix x y
    assume "B\<^sub>1 x y" and "C\<^sub>1 x y"
    show ?thesis \<proof>
  next
    fix x y
    assume "B\<^sub>2 x y" and "C\<^sub>2 x y"
    show ?thesis \<proof>
  qed
end

text \<open>Here \<open>?thesis\<close> is used to refer to the unchanged goal
  statement.\<close>


subsection \<open>Rules with cases\<close>

text \<open>
  Applying an elimination rule to some goal, leaves that unchanged
  but allows to augment the context in the sub-proof of each case.

  Isar provides some infrastructure to support this:

  \<^item> native language elements to state eliminations

  \<^item> symbolic case names

  \<^item> method @{method cases} to recover this structure in a
  sub-proof
\<close>

print_statement exE
print_statement conjE
print_statement disjE

lemma
  assumes A\<^sub>1 and A\<^sub>2  \<comment> \<open>assumptions\<close>
  obtains
    (case\<^sub>1)  x y where "B\<^sub>1 x y" and "C\<^sub>1 x y"
  | (case\<^sub>2)  x y where "B\<^sub>2 x y" and "C\<^sub>2 x y"
  \<proof>


subsubsection \<open>Example\<close>

lemma tertium_non_datur:
  obtains
    (T)  A
  | (F)  "\<not> A"
  by blast

notepad
begin
  fix x y :: 'a
  have C
  proof (cases "x = y" rule: tertium_non_datur)
    case T
    from \<open>x = y\<close> show ?thesis \<proof>
  next
    case F
    from \<open>x \<noteq> y\<close> show ?thesis \<proof>
  qed
end


subsubsection \<open>Example\<close>

text \<open>
  Isabelle/HOL specification mechanisms (datatype, inductive, etc.)
  provide suitable derived cases rules.
\<close>

datatype foo = Foo | Bar foo

notepad
begin
  fix x :: foo
  have C
  proof (cases x)
    case Foo
    from \<open>x = Foo\<close> show ?thesis \<proof>
  next
    case (Bar a)
    from \<open>x = Bar a\<close> show ?thesis \<proof>
  qed
end


subsection \<open>Elimination statements and case-splitting\<close>

text \<open>
  The @{command consider} states rules for generalized elimination and case
  splitting. This is like a toplevel statement \<^theory_text>\<open>theorem obtains\<close> used within
  a proof body; or like a multi-branch \<^theory_text>\<open>obtain\<close> without activation of the
  local context elements yet.

  The proof method @{method cases} is able to use such rules with
  forward-chaining (e.g.\ via \<^theory_text>\<open>then\<close>). This leads to the subsequent pattern
  for case-splitting in a particular situation within a proof.
\<close>

notepad
begin
  consider (a) A | (b) B | (c) C
    \<proof>  \<comment> \<open>typically \<^theory_text>\<open>by auto\<close>, \<^theory_text>\<open>by blast\<close> etc.\<close>
  then have something
  proof cases
    case a
    then show ?thesis \<proof>
  next
    case b
    then show ?thesis \<proof>
  next
    case c
    then show ?thesis \<proof>
  qed
end

subsection \<open>Obtaining local contexts\<close>

text \<open>A single ``case'' branch may be inlined into Isar proof text
  via @{command obtain}.  This proves \<^prop>\<open>(\<And>x. B x \<Longrightarrow> thesis) \<Longrightarrow>
  thesis\<close> on the spot, and augments the context afterwards.\<close>

notepad
begin
  fix B :: "'a \<Rightarrow> bool"

  obtain x where "B x" \<proof>
  note \<open>B x\<close>

  txt \<open>Conclusions from this context may not mention \<^term>\<open>x\<close> again!\<close>
  {
    obtain x where "B x" \<proof>
    from \<open>B x\<close> have C \<proof>
  }
  note \<open>C\<close>
end

end
