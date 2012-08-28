theory Framework
imports Base Main
begin

chapter {* The Isabelle/Isar Framework \label{ch:isar-framework} *}

text {*
  Isabelle/Isar
  \cite{Wenzel:1999:TPHOL,Wenzel-PhD,Nipkow-TYPES02,Wenzel-Paulson:2006,Wenzel:2006:Festschrift}
  is intended as a generic framework for developing formal
  mathematical documents with full proof checking.  Definitions and
  proofs are organized as theories.  An assembly of theory sources may
  be presented as a printed document; see also
  \chref{ch:document-prep}.

  The main objective of Isar is the design of a human-readable
  structured proof language, which is called the ``primary proof
  format'' in Isar terminology.  Such a primary proof language is
  somewhere in the middle between the extremes of primitive proof
  objects and actual natural language.  In this respect, Isar is a bit
  more formalistic than Mizar
  \cite{Trybulec:1993:MizarFeatures,Rudnicki:1992:MizarOverview,Wiedijk:1999:Mizar},
  using logical symbols for certain reasoning schemes where Mizar
  would prefer English words; see \cite{Wenzel-Wiedijk:2002} for
  further comparisons of these systems.

  So Isar challenges the traditional way of recording informal proofs
  in mathematical prose, as well as the common tendency to see fully
  formal proofs directly as objects of some logical calculus (e.g.\
  @{text "\<lambda>"}-terms in a version of type theory).  In fact, Isar is
  better understood as an interpreter of a simple block-structured
  language for describing the data flow of local facts and goals,
  interspersed with occasional invocations of proof methods.
  Everything is reduced to logical inferences internally, but these
  steps are somewhat marginal compared to the overall bookkeeping of
  the interpretation process.  Thanks to careful design of the syntax
  and semantics of Isar language elements, a formal record of Isar
  instructions may later appear as an intelligible text to the
  attentive reader.

  The Isar proof language has emerged from careful analysis of some
  inherent virtues of the existing logical framework of Isabelle/Pure
  \cite{paulson-found,paulson700}, notably composition of higher-order
  natural deduction rules, which is a generalization of Gentzen's
  original calculus \cite{Gentzen:1935}.  The approach of generic
  inference systems in Pure is continued by Isar towards actual proof
  texts.

  Concrete applications require another intermediate layer: an
  object-logic.  Isabelle/HOL \cite{isa-tutorial} (simply-typed
  set-theory) is being used most of the time; Isabelle/ZF
  \cite{isabelle-ZF} is less extensively developed, although it would
  probably fit better for classical mathematics.

  \medskip In order to illustrate natural deduction in Isar, we shall
  refer to the background theory and library of Isabelle/HOL.  This
  includes common notions of predicate logic, naive set-theory etc.\
  using fairly standard mathematical notation.  From the perspective
  of generic natural deduction there is nothing special about the
  logical connectives of HOL (@{text "\<and>"}, @{text "\<or>"}, @{text "\<forall>"},
  @{text "\<exists>"}, etc.), only the resulting reasoning principles are
  relevant to the user.  There are similar rules available for
  set-theory operators (@{text "\<inter>"}, @{text "\<union>"}, @{text "\<Inter>"}, @{text
  "\<Union>"}, etc.), or any other theory developed in the library (lattice
  theory, topology etc.).

  Subsequently we briefly review fragments of Isar proof texts
  corresponding directly to such general deduction schemes.  The
  examples shall refer to set-theory, to minimize the danger of
  understanding connectives of predicate logic as something special.

  \medskip The following deduction performs @{text "\<inter>"}-introduction,
  working forwards from assumptions towards the conclusion.  We give
  both the Isar text, and depict the primitive rule involved, as
  determined by unification of the problem against rules that are
  declared in the library context.
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
notepad
begin
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" ..
(*<*)
end
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "x \<in> A \<inter> B"}}{@{prop "x \<in> A"} & @{prop "x \<in> B"}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Note that @{command assume} augments the proof
  context, @{command then} indicates that the current fact shall be
  used in the next step, and @{command have} states an intermediate
  goal.  The two dots ``@{command ".."}'' refer to a complete proof of
  this claim, using the indicated facts and a canonical rule from the
  context.  We could have been more explicit here by spelling out the
  final proof step via the @{command "by"} command:
*}

(*<*)
notepad
begin
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" by (rule IntI)
(*<*)
end
(*>*)

text {*
  \noindent The format of the @{text "\<inter>"}-introduction rule represents
  the most basic inference, which proceeds from given premises to a
  conclusion, without any nested proof context involved.

  The next example performs backwards introduction on @{term "\<Inter>\<A>"},
  the intersection of all sets within a given set.  This requires a
  nested proof of set membership within a local context, where @{term
  A} is an arbitrary-but-fixed member of the collection:
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
notepad
begin
(*>*)
    have "x \<in> \<Inter>\<A>"
    proof
      fix A
      assume "A \<in> \<A>"
      show "x \<in> A" sorry %noproof
    qed
(*<*)
end
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "x \<in> \<Inter>\<A>"}}{\infer*{@{prop "x \<in> A"}}{@{text "[A][A \<in> \<A>]"}}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent This Isar reasoning pattern again refers to the
  primitive rule depicted above.  The system determines it in the
  ``@{command proof}'' step, which could have been spelt out more
  explicitly as ``@{command proof}~@{text "(rule InterI)"}''.  Note
  that the rule involves both a local parameter @{term "A"} and an
  assumption @{prop "A \<in> \<A>"} in the nested reasoning.  This kind of
  compound rule typically demands a genuine sub-proof in Isar, working
  backwards rather than forwards as seen before.  In the proof body we
  encounter the @{command fix}-@{command assume}-@{command show}
  outline of nested sub-proofs that is typical for Isar.  The final
  @{command show} is like @{command have} followed by an additional
  refinement of the enclosing claim, using the rule derived from the
  proof body.

  \medskip The next example involves @{term "\<Union>\<A>"}, which can be
  characterized as the set of all @{term "x"} such that @{prop "\<exists>A. x
  \<in> A \<and> A \<in> \<A>"}.  The elimination rule for @{prop "x \<in> \<Union>\<A>"} does
  not mention @{text "\<exists>"} and @{text "\<and>"} at all, but admits to obtain
  directly a local @{term "A"} such that @{prop "x \<in> A"} and @{prop "A
  \<in> \<A>"} hold.  This corresponds to the following Isar proof and
  inference rule, respectively:
*}

text_raw {*\medskip\begin{minipage}{0.6\textwidth}*}

(*<*)
notepad
begin
(*>*)
    assume "x \<in> \<Union>\<A>"
    then have C
    proof
      fix A
      assume "x \<in> A" and "A \<in> \<A>"
      show C sorry %noproof
    qed
(*<*)
end
(*>*)

text_raw {*\end{minipage}\begin{minipage}{0.4\textwidth}*}

text {*
  \infer{@{prop "C"}}{@{prop "x \<in> \<Union>\<A>"} & \infer*{@{prop "C"}~}{@{text "[A][x \<in> A, A \<in> \<A>]"}}}
*}

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Although the Isar proof follows the natural
  deduction rule closely, the text reads not as natural as
  anticipated.  There is a double occurrence of an arbitrary
  conclusion @{prop "C"}, which represents the final result, but is
  irrelevant for now.  This issue arises for any elimination rule
  involving local parameters.  Isar provides the derived language
  element @{command obtain}, which is able to perform the same
  elimination proof more conveniently:
*}

(*<*)
notepad
begin
(*>*)
    assume "x \<in> \<Union>\<A>"
    then obtain A where "x \<in> A" and "A \<in> \<A>" ..
(*<*)
end
(*>*)

text {*
  \noindent Here we avoid to mention the final conclusion @{prop "C"}
  and return to plain forward reasoning.  The rule involved in the
  ``@{command ".."}'' proof is the same as before.
*}


section {* The Pure framework \label{sec:framework-pure} *}

text {*
  The Pure logic \cite{paulson-found,paulson700} is an intuitionistic
  fragment of higher-order logic \cite{church40}.  In type-theoretic
  parlance, there are three levels of @{text "\<lambda>"}-calculus with
  corresponding arrows @{text "\<Rightarrow>"}/@{text "\<And>"}/@{text "\<Longrightarrow>"}:

  \medskip
  \begin{tabular}{ll}
  @{text "\<alpha> \<Rightarrow> \<beta>"} & syntactic function space (terms depending on terms) \\
  @{text "\<And>x. B(x)"} & universal quantification (proofs depending on terms) \\
  @{text "A \<Longrightarrow> B"} & implication (proofs depending on proofs) \\
  \end{tabular}
  \medskip

  \noindent Here only the types of syntactic terms, and the
  propositions of proof terms have been shown.  The @{text
  "\<lambda>"}-structure of proofs can be recorded as an optional feature of
  the Pure inference kernel \cite{Berghofer-Nipkow:2000:TPHOL}, but
  the formal system can never depend on them due to \emph{proof
  irrelevance}.

  On top of this most primitive layer of proofs, Pure implements a
  generic calculus for nested natural deduction rules, similar to
  \cite{Schroeder-Heister:1984}.  Here object-logic inferences are
  internalized as formulae over @{text "\<And>"} and @{text "\<Longrightarrow>"}.
  Combining such rule statements may involve higher-order unification
  \cite{paulson-natural}.
*}


subsection {* Primitive inferences *}

text {*
  Term syntax provides explicit notation for abstraction @{text "\<lambda>x ::
  \<alpha>. b(x)"} and application @{text "b a"}, while types are usually
  implicit thanks to type-inference; terms of type @{text "prop"} are
  called propositions.  Logical statements are composed via @{text "\<And>x
  :: \<alpha>. B(x)"} and @{text "A \<Longrightarrow> B"}.  Primitive reasoning operates on
  judgments of the form @{text "\<Gamma> \<turnstile> \<phi>"}, with standard introduction
  and elimination rules for @{text "\<And>"} and @{text "\<Longrightarrow>"} that refer to
  fixed parameters @{text "x\<^isub>1, \<dots>, x\<^isub>m"} and hypotheses
  @{text "A\<^isub>1, \<dots>, A\<^isub>n"} from the context @{text "\<Gamma>"};
  the corresponding proof terms are left implicit.  The subsequent
  inference rules define @{text "\<Gamma> \<turnstile> \<phi>"} inductively, relative to a
  collection of axioms:

  \[
  \infer{@{text "\<turnstile> A"}}{(@{text "A"} \text{~axiom})}
  \qquad
  \infer{@{text "A \<turnstile> A"}}{}
  \]

  \[
  \infer{@{text "\<Gamma> \<turnstile> \<And>x. B(x)"}}{@{text "\<Gamma> \<turnstile> B(x)"} & @{text "x \<notin> \<Gamma>"}}
  \qquad
  \infer{@{text "\<Gamma> \<turnstile> B(a)"}}{@{text "\<Gamma> \<turnstile> \<And>x. B(x)"}}
  \]

  \[
  \infer{@{text "\<Gamma> - A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \qquad
  \infer{@{text "\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile> B"}}{@{text "\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B"} & @{text "\<Gamma>\<^sub>2 \<turnstile> A"}}
  \]

  Furthermore, Pure provides a built-in equality @{text "\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow>
  prop"} with axioms for reflexivity, substitution, extensionality,
  and @{text "\<alpha>\<beta>\<eta>"}-conversion on @{text "\<lambda>"}-terms.

  \medskip An object-logic introduces another layer on top of Pure,
  e.g.\ with types @{text "i"} for individuals and @{text "o"} for
  propositions, term constants @{text "Trueprop :: o \<Rightarrow> prop"} as
  (implicit) derivability judgment and connectives like @{text "\<and> :: o
  \<Rightarrow> o \<Rightarrow> o"} or @{text "\<forall> :: (i \<Rightarrow> o) \<Rightarrow> o"}, and axioms for object-level
  rules such as @{text "conjI: A \<Longrightarrow> B \<Longrightarrow> A \<and> B"} or @{text "allI: (\<And>x. B
  x) \<Longrightarrow> \<forall>x. B x"}.  Derived object rules are represented as theorems of
  Pure.  After the initial object-logic setup, further axiomatizations
  are usually avoided; plain definitions and derived principles are
  used exclusively.
*}


subsection {* Reasoning with rules \label{sec:framework-resolution} *}

text {*
  Primitive inferences mostly serve foundational purposes.  The main
  reasoning mechanisms of Pure operate on nested natural deduction
  rules expressed as formulae, using @{text "\<And>"} to bind local
  parameters and @{text "\<Longrightarrow>"} to express entailment.  Multiple
  parameters and premises are represented by repeating these
  connectives in a right-associative manner.

  Since @{text "\<And>"} and @{text "\<Longrightarrow>"} commute thanks to the theorem
  @{prop "(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)"}, we may assume w.l.o.g.\
  that rule statements always observe the normal form where
  quantifiers are pulled in front of implications at each level of
  nesting.  This means that any Pure proposition may be presented as a
  \emph{Hereditary Harrop Formula} \cite{Miller:1991} which is of the
  form @{text "\<And>x\<^isub>1 \<dots> x\<^isub>m. H\<^isub>1 \<Longrightarrow> \<dots> H\<^isub>n \<Longrightarrow>
  A"} for @{text "m, n \<ge> 0"}, and @{text "A"} atomic, and @{text
  "H\<^isub>1, \<dots>, H\<^isub>n"} being recursively of the same format.
  Following the convention that outermost quantifiers are implicit,
  Horn clauses @{text "A\<^isub>1 \<Longrightarrow> \<dots> A\<^isub>n \<Longrightarrow> A"} are a special
  case of this.

  For example, @{text "\<inter>"}-introduction rule encountered before is
  represented as a Pure theorem as follows:
  \[
  @{text "IntI:"}~@{prop "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A \<inter> B"}
  \]

  \noindent This is a plain Horn clause, since no further nesting on
  the left is involved.  The general @{text "\<Inter>"}-introduction
  corresponds to a Hereditary Harrop Formula with one additional level
  of nesting:
  \[
  @{text "InterI:"}~@{prop "(\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A) \<Longrightarrow> x \<in> \<Inter>\<A>"}
  \]

  \medskip Goals are also represented as rules: @{text "A\<^isub>1 \<Longrightarrow>
  \<dots> A\<^isub>n \<Longrightarrow> C"} states that the sub-goals @{text "A\<^isub>1, \<dots>,
  A\<^isub>n"} entail the result @{text "C"}; for @{text "n = 0"} the
  goal is finished.  To allow @{text "C"} being a rule statement
  itself, we introduce the protective marker @{text "# :: prop \<Rightarrow>
  prop"}, which is defined as identity and hidden from the user.  We
  initialize and finish goal states as follows:

  \[
  \begin{array}{c@ {\qquad}c}
  \infer[(@{inference_def init})]{@{text "C \<Longrightarrow> #C"}}{} &
  \infer[(@{inference_def finish})]{@{text C}}{@{text "#C"}}
  \end{array}
  \]

  \noindent Goal states are refined in intermediate proof steps until
  a finished form is achieved.  Here the two main reasoning principles
  are @{inference resolution}, for back-chaining a rule against a
  sub-goal (replacing it by zero or more sub-goals), and @{inference
  assumption}, for solving a sub-goal (finding a short-circuit with
  local assumptions).  Below @{text "\<^vec>x"} stands for @{text
  "x\<^isub>1, \<dots>, x\<^isub>n"} (@{text "n \<ge> 0"}).

  \[
  \infer[(@{inference_def resolution})]
  {@{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> \<^vec>A (\<^vec>a \<^vec>x))\<vartheta> \<Longrightarrow> C\<vartheta>"}}
  {\begin{tabular}{rl}
    @{text "rule:"} &
    @{text "\<^vec>A \<^vec>a \<Longrightarrow> B \<^vec>a"} \\
    @{text "goal:"} &
    @{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C"} \\
    @{text "goal unifier:"} &
    @{text "(\<lambda>\<^vec>x. B (\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>"} \\
   \end{tabular}}
  \]

  \medskip

  \[
  \infer[(@{inference_def assumption})]{@{text "C\<vartheta>"}}
  {\begin{tabular}{rl}
    @{text "goal:"} &
    @{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> A \<^vec>x) \<Longrightarrow> C"} \\
    @{text "assm unifier:"} & @{text "A\<vartheta> = H\<^sub>i\<vartheta>"}~~\text{(for some~@{text "H\<^sub>i"})} \\
   \end{tabular}}
  \]

  The following trace illustrates goal-oriented reasoning in
  Isabelle/Pure:

  {\footnotesize
  \medskip
  \begin{tabular}{r@ {\quad}l}
  @{text "(A \<and> B \<Longrightarrow> B \<and> A) \<Longrightarrow> #(A \<and> B \<Longrightarrow> B \<and> A)"} & @{text "(init)"} \\
  @{text "(A \<and> B \<Longrightarrow> B) \<Longrightarrow> (A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>"} & @{text "(resolution B \<Longrightarrow> A \<Longrightarrow> B \<and> A)"} \\
  @{text "(A \<and> B \<Longrightarrow> A \<and> B) \<Longrightarrow> (A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>"} & @{text "(resolution A \<and> B \<Longrightarrow> B)"} \\
  @{text "(A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>"} & @{text "(assumption)"} \\
  @{text "(A \<and> B \<Longrightarrow> A \<and> B) \<Longrightarrow> #\<dots>"} & @{text "(resolution A \<and> B \<Longrightarrow> A)"} \\
  @{text "#\<dots>"} & @{text "(assumption)"} \\
  @{text "A \<and> B \<Longrightarrow> B \<and> A"} & @{text "(finish)"} \\
  \end{tabular}
  \medskip
  }

  Compositions of @{inference assumption} after @{inference
  resolution} occurs quite often, typically in elimination steps.
  Traditional Isabelle tactics accommodate this by a combined
  @{inference_def elim_resolution} principle.  In contrast, Isar uses
  a slightly more refined combination, where the assumptions to be
  closed are marked explicitly, using again the protective marker
  @{text "#"}:

  \[
  \infer[(@{inference refinement})]
  {@{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> \<^vec>G' (\<^vec>a \<^vec>x))\<vartheta> \<Longrightarrow> C\<vartheta>"}}
  {\begin{tabular}{rl}
    @{text "sub\<hyphen>proof:"} &
    @{text "\<^vec>G \<^vec>a \<Longrightarrow> B \<^vec>a"} \\
    @{text "goal:"} &
    @{text "(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C"} \\
    @{text "goal unifier:"} &
    @{text "(\<lambda>\<^vec>x. B (\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>"} \\
    @{text "assm unifiers:"} &
    @{text "(\<lambda>\<^vec>x. G\<^sub>j (\<^vec>a \<^vec>x))\<vartheta> = #H\<^sub>i\<vartheta>"} \\
    & \quad (for each marked @{text "G\<^sub>j"} some @{text "#H\<^sub>i"}) \\
   \end{tabular}}
  \]

  \noindent Here the @{text "sub\<hyphen>proof"} rule stems from the
  main @{command fix}-@{command assume}-@{command show} outline of
  Isar (cf.\ \secref{sec:framework-subproof}): each assumption
  indicated in the text results in a marked premise @{text "G"} above.
  The marking enforces resolution against one of the sub-goal's
  premises.  Consequently, @{command fix}-@{command assume}-@{command
  show} enables to fit the result of a sub-proof quite robustly into a
  pending sub-goal, while maintaining a good measure of flexibility.
*}


section {* The Isar proof language \label{sec:framework-isar} *}

text {*
  Structured proofs are presented as high-level expressions for
  composing entities of Pure (propositions, facts, and goals).  The
  Isar proof language allows to organize reasoning within the
  underlying rule calculus of Pure, but Isar is not another logical
  calculus!

  Isar is an exercise in sound minimalism.  Approximately half of the
  language is introduced as primitive, the rest defined as derived
  concepts.  The following grammar describes the core language
  (category @{text "proof"}), which is embedded into theory
  specification elements such as @{command theorem}; see also
  \secref{sec:framework-stmt} for the separate category @{text
  "statement"}.

  \medskip
  \begin{tabular}{rcl}
    @{text "theory\<hyphen>stmt"} & = & @{command "theorem"}~@{text "statement proof  |"}~~@{command "definition"}~@{text "\<dots>  |  \<dots>"} \\[1ex]

    @{text "proof"} & = & @{text "prfx\<^sup>*"}~@{command "proof"}~@{text "method\<^sup>? stmt\<^sup>*"}~@{command "qed"}~@{text "method\<^sup>?"} \\[1ex]

    @{text prfx} & = & @{command "using"}~@{text "facts"} \\
    & @{text "|"} & @{command "unfolding"}~@{text "facts"} \\

    @{text stmt} & = & @{command "{"}~@{text "stmt\<^sup>*"}~@{command "}"} \\
    & @{text "|"} & @{command "next"} \\
    & @{text "|"} & @{command "note"}~@{text "name = facts"} \\
    & @{text "|"} & @{command "let"}~@{text "term = term"} \\
    & @{text "|"} & @{command "fix"}~@{text "var\<^sup>+"} \\
    & @{text "|"} & @{command assume}~@{text "\<guillemotleft>inference\<guillemotright> name: props"} \\
    & @{text "|"} & @{command "then"}@{text "\<^sup>?"}~@{text goal} \\
    @{text goal} & = & @{command "have"}~@{text "name: props proof"} \\
    & @{text "|"} & @{command "show"}~@{text "name: props proof"} \\
  \end{tabular}

  \medskip Simultaneous propositions or facts may be separated by the
  @{keyword "and"} keyword.

  \medskip The syntax for terms and propositions is inherited from
  Pure (and the object-logic).  A @{text "pattern"} is a @{text
  "term"} with schematic variables, to be bound by higher-order
  matching.

  \medskip Facts may be referenced by name or proposition.  For
  example, the result of ``@{command have}~@{text "a: A \<langle>proof\<rangle>"}''
  becomes available both as @{text "a"} and
  \isacharbackquoteopen@{text "A"}\isacharbackquoteclose.  Moreover,
  fact expressions may involve attributes that modify either the
  theorem or the background context.  For example, the expression
  ``@{text "a [OF b]"}'' refers to the composition of two facts
  according to the @{inference resolution} inference of
  \secref{sec:framework-resolution}, while ``@{text "a [intro]"}''
  declares a fact as introduction rule in the context.

  The special fact called ``@{fact this}'' always refers to the last
  result, as produced by @{command note}, @{command assume}, @{command
  have}, or @{command show}.  Since @{command note} occurs
  frequently together with @{command then} we provide some
  abbreviations:

  \medskip
  \begin{tabular}{rcl}
    @{command from}~@{text a} & @{text "\<equiv>"} & @{command note}~@{text a}~@{command then} \\
    @{command with}~@{text a} & @{text "\<equiv>"} & @{command from}~@{text "a \<AND> this"} \\
  \end{tabular}
  \medskip

  The @{text "method"} category is essentially a parameter and may be
  populated later.  Methods use the facts indicated by @{command
  "then"} or @{command using}, and then operate on the goal state.
  Some basic methods are predefined: ``@{method "-"}'' leaves the goal
  unchanged, ``@{method this}'' applies the facts as rules to the
  goal, ``@{method (Pure) "rule"}'' applies the facts to another rule and the
  result to the goal (both ``@{method this}'' and ``@{method (Pure) rule}''
  refer to @{inference resolution} of
  \secref{sec:framework-resolution}).  The secondary arguments to
  ``@{method (Pure) rule}'' may be specified explicitly as in ``@{text "(rule
  a)"}'', or picked from the context.  In the latter case, the system
  first tries rules declared as @{attribute (Pure) elim} or
  @{attribute (Pure) dest}, followed by those declared as @{attribute
  (Pure) intro}.

  The default method for @{command proof} is ``@{method (Pure) rule}''
  (arguments picked from the context), for @{command qed} it is
  ``@{method "-"}''.  Further abbreviations for terminal proof steps
  are ``@{command "by"}~@{text "method\<^sub>1 method\<^sub>2"}'' for
  ``@{command proof}~@{text "method\<^sub>1"}~@{command qed}~@{text
  "method\<^sub>2"}'', and ``@{command ".."}'' for ``@{command
  "by"}~@{method (Pure) rule}, and ``@{command "."}'' for ``@{command
  "by"}~@{method this}''.  The @{command unfolding} element operates
  directly on the current facts and goal by applying equalities.

  \medskip Block structure can be indicated explicitly by ``@{command
  "{"}~@{text "\<dots>"}~@{command "}"}'', although the body of a sub-proof
  already involves implicit nesting.  In any case, @{command next}
  jumps into the next section of a block, i.e.\ it acts like closing
  an implicit block scope and opening another one; there is no direct
  correspondence to subgoals here.

  The remaining elements @{command fix} and @{command assume} build up
  a local context (see \secref{sec:framework-context}), while
  @{command show} refines a pending sub-goal by the rule resulting
  from a nested sub-proof (see \secref{sec:framework-subproof}).
  Further derived concepts will support calculational reasoning (see
  \secref{sec:framework-calc}).
*}


subsection {* Context elements \label{sec:framework-context} *}

text {*
  In judgments @{text "\<Gamma> \<turnstile> \<phi>"} of the primitive framework, @{text "\<Gamma>"}
  essentially acts like a proof context.  Isar elaborates this idea
  towards a higher-level notion, with additional information for
  type-inference, term abbreviations, local facts, hypotheses etc.

  The element @{command fix}~@{text "x :: \<alpha>"} declares a local
  parameter, i.e.\ an arbitrary-but-fixed entity of a given type; in
  results exported from the context, @{text "x"} may become anything.
  The @{command assume}~@{text "\<guillemotleft>inference\<guillemotright>"} element provides a
  general interface to hypotheses: ``@{command assume}~@{text
  "\<guillemotleft>inference\<guillemotright> A"}'' produces @{text "A \<turnstile> A"} locally, while the
  included inference tells how to discharge @{text A} from results
  @{text "A \<turnstile> B"} later on.  There is no user-syntax for @{text
  "\<guillemotleft>inference\<guillemotright>"}, i.e.\ it may only occur internally when derived
  commands are defined in ML.

  At the user-level, the default inference for @{command assume} is
  @{inference discharge} as given below.  The additional variants
  @{command presume} and @{command def} are defined as follows:

  \medskip
  \begin{tabular}{rcl}
    @{command presume}~@{text A} & @{text "\<equiv>"} & @{command assume}~@{text "\<guillemotleft>weak\<hyphen>discharge\<guillemotright> A"} \\
    @{command def}~@{text "x \<equiv> a"} & @{text "\<equiv>"} & @{command fix}~@{text x}~@{command assume}~@{text "\<guillemotleft>expansion\<guillemotright> x \<equiv> a"} \\
  \end{tabular}
  \medskip

  \[
  \infer[(@{inference_def discharge})]{@{text "\<strut>\<Gamma> - A \<turnstile> #A \<Longrightarrow> B"}}{@{text "\<strut>\<Gamma> \<turnstile> B"}}
  \]
  \[
  \infer[(@{inference_def "weak\<hyphen>discharge"})]{@{text "\<strut>\<Gamma> - A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<strut>\<Gamma> \<turnstile> B"}}
  \]
  \[
  \infer[(@{inference_def expansion})]{@{text "\<strut>\<Gamma> - (x \<equiv> a) \<turnstile> B a"}}{@{text "\<strut>\<Gamma> \<turnstile> B x"}}
  \]

  \medskip Note that @{inference discharge} and @{inference
  "weak\<hyphen>discharge"} differ in the marker for @{prop A}, which is
  relevant when the result of a @{command fix}-@{command
  assume}-@{command show} outline is composed with a pending goal,
  cf.\ \secref{sec:framework-subproof}.

  The most interesting derived context element in Isar is @{command
  obtain} \cite[\S5.3]{Wenzel-PhD}, which supports generalized
  elimination steps in a purely forward manner.  The @{command obtain}
  command takes a specification of parameters @{text "\<^vec>x"} and
  assumptions @{text "\<^vec>A"} to be added to the context, together
  with a proof of a case rule stating that this extension is
  conservative (i.e.\ may be removed from closed results later on):

  \medskip
  \begin{tabular}{l}
  @{text "\<langle>facts\<rangle>"}~~@{command obtain}~@{text "\<^vec>x \<WHERE> \<^vec>A \<^vec>x  \<langle>proof\<rangle> \<equiv>"} \\[0.5ex]
  \quad @{command have}~@{text "case: \<And>thesis. (\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis) \<Longrightarrow> thesis\<rangle>"} \\
  \quad @{command proof}~@{method "-"} \\
  \qquad @{command fix}~@{text thesis} \\
  \qquad @{command assume}~@{text "[intro]: \<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis"} \\
  \qquad @{command show}~@{text thesis}~@{command using}~@{text "\<langle>facts\<rangle> \<langle>proof\<rangle>"} \\
  \quad @{command qed} \\
  \quad @{command fix}~@{text "\<^vec>x"}~@{command assume}~@{text "\<guillemotleft>elimination case\<guillemotright> \<^vec>A \<^vec>x"} \\
  \end{tabular}
  \medskip

  \[
  \infer[(@{inference elimination})]{@{text "\<Gamma> \<turnstile> B"}}{
    \begin{tabular}{rl}
    @{text "case:"} &
    @{text "\<Gamma> \<turnstile> \<And>thesis. (\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis) \<Longrightarrow> thesis"} \\[0.2ex]
    @{text "result:"} &
    @{text "\<Gamma> \<union> \<^vec>A \<^vec>y \<turnstile> B"} \\[0.2ex]
    \end{tabular}}
  \]

  \noindent Here the name ``@{text thesis}'' is a specific convention
  for an arbitrary-but-fixed proposition; in the primitive natural
  deduction rules shown before we have occasionally used @{text C}.
  The whole statement of ``@{command obtain}~@{text x}~@{keyword
  "where"}~@{text "A x"}'' may be read as a claim that @{text "A x"}
  may be assumed for some arbitrary-but-fixed @{text "x"}.  Also note
  that ``@{command obtain}~@{text "A \<AND> B"}'' without parameters
  is similar to ``@{command have}~@{text "A \<AND> B"}'', but the
  latter involves multiple sub-goals.

  \medskip The subsequent Isar proof texts explain all context
  elements introduced above using the formal proof language itself.
  After finishing a local proof within a block, we indicate the
  exported result via @{command note}.
*}

(*<*)
theorem True
proof
(*>*)
  txt_raw {* \begin{minipage}[t]{0.45\textwidth} *}
  {
    fix x
    have "B x" sorry %noproof
  }
  note `\<And>x. B x`
  txt_raw {* \end{minipage}\quad\begin{minipage}[t]{0.45\textwidth} *}(*<*)next(*>*)
  {
    assume A
    have B sorry %noproof
  }
  note `A \<Longrightarrow> B`
  txt_raw {* \end{minipage}\\[3ex]\begin{minipage}[t]{0.45\textwidth} *}(*<*)next(*>*)
  {
    def x \<equiv> a
    have "B x" sorry %noproof
  }
  note `B a`
  txt_raw {* \end{minipage}\quad\begin{minipage}[t]{0.45\textwidth} *}(*<*)next(*>*)
  {
    obtain x where "A x" sorry %noproof
    have B sorry %noproof
  }
  note `B`
  txt_raw {* \end{minipage} *}
(*<*)
qed
(*>*)

text {*
  \bigskip\noindent This illustrates the meaning of Isar context
  elements without goals getting in between.
*}

subsection {* Structured statements \label{sec:framework-stmt} *}

text {*
  The category @{text "statement"} of top-level theorem specifications
  is defined as follows:

  \medskip
  \begin{tabular}{rcl}
  @{text "statement"} & @{text "\<equiv>"} & @{text "name: props \<AND> \<dots>"} \\
  & @{text "|"} & @{text "context\<^sup>* conclusion"} \\[0.5ex]

  @{text "context"} & @{text "\<equiv>"} & @{text "\<FIXES> vars \<AND> \<dots>"} \\
  & @{text "|"} & @{text "\<ASSUMES> name: props \<AND> \<dots>"} \\

  @{text "conclusion"} & @{text "\<equiv>"} & @{text "\<SHOWS> name: props \<AND> \<dots>"} \\
  & @{text "|"} & @{text "\<OBTAINS> vars \<AND> \<dots> \<WHERE> name: props \<AND> \<dots>"} \\
  & & \quad @{text "\<BBAR> \<dots>"} \\
  \end{tabular}

  \medskip\noindent A simple @{text "statement"} consists of named
  propositions.  The full form admits local context elements followed
  by the actual conclusions, such as ``@{keyword "fixes"}~@{text
  x}~@{keyword "assumes"}~@{text "A x"}~@{keyword "shows"}~@{text "B
  x"}''.  The final result emerges as a Pure rule after discharging
  the context: @{prop "\<And>x. A x \<Longrightarrow> B x"}.

  The @{keyword "obtains"} variant is another abbreviation defined
  below; unlike @{command obtain} (cf.\
  \secref{sec:framework-context}) there may be several ``cases''
  separated by ``@{text "\<BBAR>"}'', each consisting of several
  parameters (@{text "vars"}) and several premises (@{text "props"}).
  This specifies multi-branch elimination rules.

  \medskip
  \begin{tabular}{l}
  @{text "\<OBTAINS> \<^vec>x \<WHERE> \<^vec>A \<^vec>x   \<BBAR>   \<dots>   \<equiv>"} \\[0.5ex]
  \quad @{text "\<FIXES> thesis"} \\
  \quad @{text "\<ASSUMES> [intro]: \<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis  \<AND>  \<dots>"} \\
  \quad @{text "\<SHOWS> thesis"} \\
  \end{tabular}
  \medskip

  Presenting structured statements in such an ``open'' format usually
  simplifies the subsequent proof, because the outer structure of the
  problem is already laid out directly.  E.g.\ consider the following
  canonical patterns for @{text "\<SHOWS>"} and @{text "\<OBTAINS>"},
  respectively:
*}

text_raw {*\begin{minipage}{0.5\textwidth}*}

theorem
  fixes x and y
  assumes "A x" and "B y"
  shows "C x y"
proof -
  from `A x` and `B y`
  show "C x y" sorry %noproof
qed

text_raw {*\end{minipage}\begin{minipage}{0.5\textwidth}*}

theorem
  obtains x and y
  where "A x" and "B y"
proof -
  have "A a" and "B b" sorry %noproof
  then show thesis ..
qed

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Here local facts \isacharbackquoteopen@{text "A
  x"}\isacharbackquoteclose\ and \isacharbackquoteopen@{text "B
  y"}\isacharbackquoteclose\ are referenced immediately; there is no
  need to decompose the logical rule structure again.  In the second
  proof the final ``@{command then}~@{command show}~@{text
  thesis}~@{command ".."}''  involves the local rule case @{text "\<And>x
  y. A x \<Longrightarrow> B y \<Longrightarrow> thesis"} for the particular instance of terms @{text
  "a"} and @{text "b"} produced in the body.
*}


subsection {* Structured proof refinement \label{sec:framework-subproof} *}

text {*
  By breaking up the grammar for the Isar proof language, we may
  understand a proof text as a linear sequence of individual proof
  commands.  These are interpreted as transitions of the Isar virtual
  machine (Isar/VM), which operates on a block-structured
  configuration in single steps.  This allows users to write proof
  texts in an incremental manner, and inspect intermediate
  configurations for debugging.

  The basic idea is analogous to evaluating algebraic expressions on a
  stack machine: @{text "(a + b) \<cdot> c"} then corresponds to a sequence
  of single transitions for each symbol @{text "(, a, +, b, ), \<cdot>, c"}.
  In Isar the algebraic values are facts or goals, and the operations
  are inferences.

  \medskip The Isar/VM state maintains a stack of nodes, each node
  contains the local proof context, the linguistic mode, and a pending
  goal (optional).  The mode determines the type of transition that
  may be performed next, it essentially alternates between forward and
  backward reasoning, with an intermediate stage for chained facts
  (see \figref{fig:isar-vm}).

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{isar-vm}
  \end{center}
  \caption{Isar/VM modes}\label{fig:isar-vm}
  \end{figure}

  For example, in @{text "state"} mode Isar acts like a mathematical
  scratch-pad, accepting declarations like @{command fix}, @{command
  assume}, and claims like @{command have}, @{command show}.  A goal
  statement changes the mode to @{text "prove"}, which means that we
  may now refine the problem via @{command unfolding} or @{command
  proof}.  Then we are again in @{text "state"} mode of a proof body,
  which may issue @{command show} statements to solve pending
  sub-goals.  A concluding @{command qed} will return to the original
  @{text "state"} mode one level upwards.  The subsequent Isar/VM
  trace indicates block structure, linguistic mode, goal state, and
  inferences:
*}

text_raw {* \begingroup\footnotesize *}
(*<*)notepad begin
(*>*)
  txt_raw {* \begin{minipage}[t]{0.18\textwidth} *}
  have "A \<longrightarrow> B"
  proof
    assume A
    show B
      sorry %noproof
  qed
  txt_raw {* \end{minipage}\quad
\begin{minipage}[t]{0.06\textwidth}
@{text "begin"} \\
\\
\\
@{text "begin"} \\
@{text "end"} \\
@{text "end"} \\
\end{minipage}
\begin{minipage}[t]{0.08\textwidth}
@{text "prove"} \\
@{text "state"} \\
@{text "state"} \\
@{text "prove"} \\
@{text "state"} \\
@{text "state"} \\
\end{minipage}\begin{minipage}[t]{0.35\textwidth}
@{text "(A \<longrightarrow> B) \<Longrightarrow> #(A \<longrightarrow> B)"} \\
@{text "(A \<Longrightarrow> B) \<Longrightarrow> #(A \<longrightarrow> B)"} \\
\\
\\
@{text "#(A \<longrightarrow> B)"} \\
@{text "A \<longrightarrow> B"} \\
\end{minipage}\begin{minipage}[t]{0.4\textwidth}
@{text "(init)"} \\
@{text "(resolution impI)"} \\
\\
\\
@{text "(refinement #A \<Longrightarrow> B)"} \\
@{text "(finish)"} \\
\end{minipage} *}
(*<*)
end
(*>*)
text_raw {* \endgroup *}

text {*
  \noindent Here the @{inference refinement} inference from
  \secref{sec:framework-resolution} mediates composition of Isar
  sub-proofs nicely.  Observe that this principle incorporates some
  degree of freedom in proof composition.  In particular, the proof
  body allows parameters and assumptions to be re-ordered, or commuted
  according to Hereditary Harrop Form.  Moreover, context elements
  that are not used in a sub-proof may be omitted altogether.  For
  example:
*}

text_raw {*\begin{minipage}{0.5\textwidth}*}

(*<*)
notepad
begin
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix x and y
    assume "A x" and "B y"
    show "C x y" sorry %noproof
  qed

txt_raw {*\end{minipage}\begin{minipage}{0.5\textwidth}*}

(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix x assume "A x"
    fix y assume "B y"
    show "C x y" sorry %noproof
  qed

txt_raw {*\end{minipage}\\[3ex]\begin{minipage}{0.5\textwidth}*}

(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix y assume "B y"
    fix x assume "A x"
    show "C x y" sorry
  qed

txt_raw {*\end{minipage}\begin{minipage}{0.5\textwidth}*}
(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix y assume "B y"
    fix x
    show "C x y" sorry
  qed
(*<*)
end
(*>*)

text_raw {*\end{minipage}*}

text {*
  \medskip\noindent Such ``peephole optimizations'' of Isar texts are
  practically important to improve readability, by rearranging
  contexts elements according to the natural flow of reasoning in the
  body, while still observing the overall scoping rules.

  \medskip This illustrates the basic idea of structured proof
  processing in Isar.  The main mechanisms are based on natural
  deduction rule composition within the Pure framework.  In
  particular, there are no direct operations on goal states within the
  proof body.  Moreover, there is no hidden automated reasoning
  involved, just plain unification.
*}


subsection {* Calculational reasoning \label{sec:framework-calc} *}

text {*
  The existing Isar infrastructure is sufficiently flexible to support
  calculational reasoning (chains of transitivity steps) as derived
  concept.  The generic proof elements introduced below depend on
  rules declared as @{attribute trans} in the context.  It is left to
  the object-logic to provide a suitable rule collection for mixed
  relations of @{text "="}, @{text "<"}, @{text "\<le>"}, @{text "\<subset>"},
  @{text "\<subseteq>"} etc.  Due to the flexibility of rule composition
  (\secref{sec:framework-resolution}), substitution of equals by
  equals is covered as well, even substitution of inequalities
  involving monotonicity conditions; see also \cite[\S6]{Wenzel-PhD}
  and \cite{Bauer-Wenzel:2001}.

  The generic calculational mechanism is based on the observation that
  rules such as @{text "trans:"}~@{prop "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"}
  proceed from the premises towards the conclusion in a deterministic
  fashion.  Thus we may reason in forward mode, feeding intermediate
  results into rules selected from the context.  The course of
  reasoning is organized by maintaining a secondary fact called
  ``@{fact calculation}'', apart from the primary ``@{fact this}''
  already provided by the Isar primitives.  In the definitions below,
  @{attribute OF} refers to @{inference resolution}
  (\secref{sec:framework-resolution}) with multiple rule arguments,
  and @{text "trans"} represents to a suitable rule from the context:

  \begin{matharray}{rcl}
    @{command "also"}@{text "\<^sub>0"} & \equiv & @{command "note"}~@{text "calculation = this"} \\
    @{command "also"}@{text "\<^sub>n\<^sub>+\<^sub>1"} & \equiv & @{command "note"}~@{text "calculation = trans [OF calculation this]"} \\[0.5ex]
    @{command "finally"} & \equiv & @{command "also"}~@{command "from"}~@{text calculation} \\
  \end{matharray}

  \noindent The start of a calculation is determined implicitly in the
  text: here @{command also} sets @{fact calculation} to the current
  result; any subsequent occurrence will update @{fact calculation} by
  combination with the next result and a transitivity rule.  The
  calculational sequence is concluded via @{command finally}, where
  the final result is exposed for use in a concluding claim.

  Here is a canonical proof pattern, using @{command have} to
  establish the intermediate results:
*}

(*<*)
notepad
begin
(*>*)
  have "a = b" sorry
  also have "\<dots> = c" sorry
  also have "\<dots> = d" sorry
  finally have "a = d" .
(*<*)
end
(*>*)

text {*
  \noindent The term ``@{text "\<dots>"}'' above is a special abbreviation
  provided by the Isabelle/Isar syntax layer: it statically refers to
  the right-hand side argument of the previous statement given in the
  text.  Thus it happens to coincide with relevant sub-expressions in
  the calculational chain, but the exact correspondence is dependent
  on the transitivity rules being involved.

  \medskip Symmetry rules such as @{prop "x = y \<Longrightarrow> y = x"} are like
  transitivities with only one premise.  Isar maintains a separate
  rule collection declared via the @{attribute sym} attribute, to be
  used in fact expressions ``@{text "a [symmetric]"}'', or single-step
  proofs ``@{command assume}~@{text "x = y"}~@{command then}~@{command
  have}~@{text "y = x"}~@{command ".."}''.
*}

end