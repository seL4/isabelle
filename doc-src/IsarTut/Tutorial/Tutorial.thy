
(*<*)
theory Tutorial = Main:
(*>*)

chapter {* Introduction *}

chapter {* Interaction and debugging *}

chapter {* Calculational reasoning *}

chapter {* Proof by cases and induction *}

chapter {* General natural deduction *}

chapter {* Example: FIXME *}


chapter FIXME


section {* Formal document preparation *}

subsection {* Example *}

text {*
  See this very document itself.
*}

subsection {* Getting started *}

text {*
  \verb"isatool mkdir Test && isatool make"
*}

section {* Human-readable proof composition in Isar *}

subsection {* Getting started *}

text {* Claim a trivial goal in order to enter proof mode @{text \<dots>} *}

lemma True
proof

  txt {* After the canonical initial refinement step we are left
    within an \emph{proof body}. *}

  txt {* Here we may augment the present local {proof context} as we
    please. *}

  fix something
  assume a: "anything something"

  txt {* Note that the present configuration may be inspected by
  several \emph{diagnostic commands}. *}

  term something  -- "@{term [show_types] something}"
  term anything  -- "@{term [show_types] anything}"
  thm a  -- {* @{thm a} *}

  txt {* We may state local (auxiliary) results as well. *}

  have True proof qed

  txt {* We are now satisfied. *}
qed


subsection {* Calculational Reasoning *}

text {*
  Isar is mainly about Natural Deduction, but Calculational Reasoning
  turns out as a simplified instance of that, so we demonstrate it
  first.
*}

subsubsection {* Transitive chains *}

text {*
  Technique: establish a chain of local facts, separated by \cmd{also}
  and terminated by \cmd{finally}; another goal has to follow to point
  out the final result.
*}

lemma "x1 = x4"
proof -  -- "do nothing yet"
  have "x1 = x2" sorry
  also
  have "x2 = x3" sorry
  also
  have "x3 = x4" sorry
  finally
  show "x1 = x4" .
qed

text {*
  This may be written more succinctly, using the special term binds
  ``@{text \<dots>}'' (for the right-hand side of the last statement) and
  ``@{text ?thesis}'' (for the original claim at the head of the
  proof).
*}

lemma "x1 = x4"
proof -
  have "x1 = x2" sorry
  also have "\<dots> = x3" sorry
  also have "\<dots> = x4" sorry
  finally show ?thesis .
qed

text {*
  The (implicit) forward-chaining steps involved in \cmd{also} and
  \cmd{finally} are declared in the current context.  The main library
  of Isabelle/HOL already knows about (mixed) transitivities of @{text
  "="}, @{text "<"}, @{text "\<le>"} etc.
*}

lemma "(x1::nat) < x6"
  -- {* restriction to type @{typ nat} ensures that @{text "<"} is really transitive *}
proof -
  have "x1 < x2" sorry
  also have "\<dots> \<le> x3" sorry
  also have "\<dots> = x4" sorry
  also have "\<dots> < x5" sorry
  also have "\<dots> = x6" sorry
  finally show ?thesis .
qed

text {*
  We may also calculate on propositions.
*}

lemma True
proof
  have "A \<longrightarrow> B \<longrightarrow> C" sorry
  also have A sorry
  also have B sorry
  finally have C .
qed    

text {*
  This is getting pretty close to Dijkstra's preferred proof style.
*}

lemma True
proof
  have [trans]: "\<And>X Y Z. X \<longrightarrow> Y \<Longrightarrow> Y \<longrightarrow> Z \<Longrightarrow> X \<longrightarrow> Z" by rules
  have "A \<longrightarrow> B" sorry
  also have "\<dots> \<longrightarrow> C" sorry
  also have "\<dots> \<longrightarrow> D" sorry
  finally have "A \<longrightarrow> D" .
qed


subsubsection {* Degenerate calculations and bigstep reasoning *}

text {*
  Instead of \cmd{also}/\cmd{finally} we may use degenerative steps
  \cmd{moreover}/\cmd{ultimately} to accumulate facts, without
  applying any forward rules yet.
*}

lemma True
proof
  have A sorry
  moreover have B sorry
  moreover have C sorry
  ultimately have A and B and C .  -- "Pretty obvious, right?"
qed

text {*
  Both kinds of calculational elements may be used together.
*}

lemma True
proof
  assume reasoning_pattern [trans]: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D"
  have A sorry
  moreover have B sorry
  moreover have C sorry
  finally have D .
qed
  

subsection {* Natural deduction *}

subsubsection {* Primitive patterns *}

text {*
  The default theory context admits to perform canonical single-step
  reasoning (similar to Gentzen) without further ado.
*}

lemma True
proof

  have True ..

  { assume False
    then have C .. }

  have "\<not> A"
  proof
    assume A
    show False sorry
  qed

  { assume "\<not> A" and A
    then have C .. }

  have "A \<longrightarrow> B"
  proof
    assume A
    show B sorry
  qed

  { assume "A \<longrightarrow> B" and A
    then have B .. }

  have "A \<and> B"
  proof
    show A sorry
    show B sorry
  qed

  { assume "A \<and> B"
    then have A .. }

  { assume "A \<and> B"
    then have B .. }

  { assume A
    then have "A \<or> B" .. }

  { assume B
    then have "A \<or> B" .. }

  { assume "A \<or> B"
    then have C
    proof
      assume A
      then show ?thesis sorry
    next
      assume B
      then show ?thesis sorry
    qed }

  have "\<forall>x. P x"
  proof
    fix x
    show "P x" sorry
  qed

  { assume "\<forall>x. P x"
    then have "P t" .. }

  have "\<exists>x. P x"
  proof
    show "P t" sorry
  qed
  
  { assume "\<exists>x. P x"
    then obtain x where "P x" ..
    note nothing  -- "relax" }
qed

text {*
  Certainly, this works with derived rules for defined concepts in the
  same manner.  E.g.\ use the simple-typed set-theory of Isabelle/HOL. *}

lemma True
proof
  have "y \<in> (\<Inter>x \<in> A. B x)"
  proof
    fix x
    assume "x \<in> A"
    show "y \<in> B x" sorry
  qed

  have "y \<in> (\<Union>x \<in> A. B x)"
  proof
    show "a \<in> A" sorry
    show "y \<in> B a" sorry
  qed
qed


subsubsection {* Variations in structure *}

text {*
  The design of the Isar language takes the user seriously
*}

subsubsection {* Generalized elimination *}

subsubsection {* Scalable cases and induction *}

section {* Assimilating the old tactical style *}

text {*
  Improper commands: 
  Observation: every Isar subproof may start with a ``script'' of
*}

(*<*)
end
(*>*)
