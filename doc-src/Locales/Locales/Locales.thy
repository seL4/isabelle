(*
  Title:  Locales in Isabelle/Isar
  Id:	  $Id$
  Author: Clemens Ballarin, started 31 January 2003
  Copyright (c) 2003 by Clemens Ballarin
*)

(*<*)
theory Locales = Main:

ML_setup {* print_mode := "type_brackets" :: !print_mode; *}
(*>*)

section {* Overview *}

text {*
  Locales are an extension of the Isabelle proof assistant.  They
  provide support for modular reasoning. Locales were initially
  developed by Kamm\"uller~\cite{Kammuller2000} to support reasoning
  in abstract algebra, but are applied also in other domains --- for
  example, bytecode verification~\cite{Klein2003}.

  Kamm\"uller's original design, implemented in Isabelle99, provides, in
  addition to
  means for declaring locales, a set of ML functions that were used
  along with ML tactics in a proof.  In the meantime, the input format
  for proof in Isabelle has changed and users write proof
  scripts in ML only rarely if at all.  Two new proof styles are
  available, and can
  be used interchangeably: linear proof scripts that closely resemble ML
  tactics, and the structured Isar proof language by
  Wenzel~\cite{Wenzel2002a}.  Subsequently, Wenzel re-implemented
  locales for
  the new proof format.  The implementation, available with
  Isabelle2003, constitutes a complete re-design and exploits that
  both Isar and locales are based on the notion of context,
  and thus locales are seen as a natural extension of Isar.
  Nevertheless, locales can also be used with proof scripts:
  their use does not require a deep understanding of the structured
  Isar proof style.

  At the same time, Wenzel considerably extended locales.  The most
  important addition are locale expressions, which allow to combine
  locales more freely.  Previously only
  linear inheritance was possible.  Now locales support multiple
  inheritance through a normalisation algorithm.  New are also
  structures, which provide special syntax for locale parameters that
  represent algebraic structures.

  Unfortunately, Wenzel provided only an implementation but hardly any
  documentation.  Besides providing documentation, the present paper
  is a high-level description of locales, and in particular locale
  expressions.  It is meant as a first step towards the semantics of
  locales, and also as a base for comparing locales with module concepts
  in other provers.  It also constitutes the base for future
  extensions of locales in Isabelle.
  The description was derived mainly by experimenting
  with locales and partially also by inspecting the code.

  The main contribution of the author of the present paper is the
  abstract description of Wenzel's version of locales, and in
  particular of the normalisation algorithm for locale expressions (see
  Section~\ref{sec-normal-forms}).  Contributions to the
  implementation are confined to bug fixes and to provisions that
  enable the use of locales with linear proof scripts.

  Concepts are introduced along with examples, so that the text can be
  used as tutorial.  It is assumed that the reader is somewhat
  familiar with Isabelle proof scripts.  Examples have been phrased as
  structured
  Isar proofs.  However, in order to understand the key concepts,
  including locales expressions and their normalisation, detailed
  knowledge of Isabelle is not necessary. 

\nocite{Nipkow2003,Wenzel2002b,Wenzel2003}
*}

section {* Locales: Beyond Proof Contexts *}

text {*
  In tactic-based provers the application of a sequence of proof
  tactics leads to a proof state.  This state is usually hard to
  predict from looking at the tactic script, unless one replays the
  proof step-by-step.  The structured proof language Isar is
  different.  It is additionally based on \emph{proof contexts},
  which are directly visible in Isar scripts, and since tactic
  sequences tend to be short, this commonly leads to clearer proof
  scripts.

  Goals are stated with the \textbf{theorem}
  command.  This is followed by a proof.  When discharging a goal
  requires an elaborate argument
  (rather than the application of a single tactic) a new context
  may be entered (\textbf{proof}).  Inside the context, variables may
  be fixed (\textbf{fix}), assumptions made (\textbf{assume}) and
  intermediate goals stated (\textbf{have}) and proved.  The
  assumptions must be dischargeable by premises of the surrounding
  goal, and once this goal has been proved (\textbf{show}) the proof context
  can be closed (\textbf{qed}). Contexts inherit from surrounding
  contexts, but it is not possible
  to export from them (with exception of the proved goal);
  they ``disappear'' after the closing \textbf{qed}.
  Facts may have attributes --- for example, identifying them as
  default to the simplifier or classical reasoner.

  Locales extend proof contexts in various ways:
  \begin{itemize}
  \item
    Locales are usually \emph{named}.  This makes them persistent.
  \item
    Fixed variables may have \emph{syntax}.
  \item
    It is possible to \emph{add} and \emph{export} facts.
  \item
    Locales can be combined and modified with \emph{locale
    expressions}.
  \end{itemize}
  The Locales facility extends the Isar language: it provides new ways
  of stating and managing facts, but it does not modify the language
  for proofs.  Its purpose is to support writing modular proofs.
*}

section {* Simple Locales *}

subsection {* Syntax and Terminology *}

text {*
  The grammar of Isar is extended by commands for locales as shown in
  Figure~\ref{fig-grammar}.
  A key concept, introduced by Wenzel, is that
  locales are (internally) lists
  of \emph{context elements}.  There are four kinds, identified
  by the keywords \textbf{fixes}, \textbf{assumes}, \textbf{defines} and
  \textbf{notes}.

  \begin{figure}
  \hrule
  \vspace{2ex}
  \begin{small}
  \begin{tabular}{l>$c<$l}
  \textit{attr-name} & ::=
  & \textit{name} $|$ \textit{attribute} $|$
    \textit{name} \textit{attribute} \\

  \textit{locale-expr}  & ::= 
  & \textit{locale-expr1} ( ``\textbf{+}'' \textit{locale-expr1} )$^*$ \\
  \textit{locale-expr1} & ::=
  & ( \textit{qualified-name} $|$
    ``\textbf{(}'' \textit{locale-expr} ``\textbf{)}'' )
    ( \textit{name} $|$ ``\textbf{\_}'' )$^*$ \\

  \textit{fixes} & ::=
  & \textit{name} [ ``\textbf{::}'' \textit{type} ]
    [ ``\textbf{(}'' \textbf{structure} ``\textbf{)}'' $|$
    \textit{mixfix} ] \\
  \textit{assumes} & ::=
  & [ \textit{attr-name} ``\textbf{:}'' ] \textit{proposition} \\
  \textit{defines} & ::=
  & [ \textit{attr-name} ``\textbf{:}'' ] \textit{proposition} \\
  \textit{notes} & ::=
  & [ \textit{attr-name} ``\textbf{=}'' ]
    ( \textit{qualified-name} [ \textit{attribute} ] )$^+$ \\

  \textit{element} & ::=
  & \textbf{fixes} \textit{fixes} ( \textbf{and} \textit{fixes} )$^*$ \\
  & |
  & \textbf{assumes} \textit{assumes} ( \textbf{and} \textit{assumes} )$^*$ \\
  & |
  & \textbf{defines} \textit{defines} ( \textbf{and} \textit{defines} )$^*$ \\
  & |
  & \textbf{notes} \textit{notes} ( \textbf{and} \textit{notes} )$^*$ \\
  & | & \textbf{includes} \textit{locale-expr} \\

  \textit{locale} & ::=
  & \textit{element}$^+$ \\
  & | & \textit{locale-expr} [ ``\textbf{+}'' \textit{element}$^+$ ] \\

  \textit{in-target} & ::=
  & ``\textbf{(}'' \textbf{in} \textit{qualified-name} ``\textbf{)}'' \\

  \textit{theorem} & ::= & ( \textbf{theorem} $|$ \textbf{lemma} $|$
    \textbf{corollary} ) [ \textit{in-target} ] [ \textit{attr-name} ] \\

  \textit{theory-level} & ::= & \ldots \\
  & | & \textbf{locale} \textit{name} [ ``\textbf{=}''
    \textit{locale} ] \\
  % note: legacy "locale (open)" omitted.
  & | & ( \textbf{theorems} $|$ \textbf{lemmas} ) \\
  & & [ \textit{in-target} ] [ \textit{attr-name} ``\textbf{=}'' ]
    ( \textit{qualified-name} [ \textit{attribute} ] )$^+$ \\
  & | & \textbf{declare} [ \textit{in-target} ] ( \textit{qualified-name}
    [ \textit{attribute} ] )$^+$ \\
  & | & \textit{theorem} \textit{proposition} \textit{proof} \\
  & | & \textit{theorem} \textit{element}$^*$
    \textbf{shows} \textit{proposition} \textit{proof} \\
  & | & \textbf{print\_locale} \textit{locale} \\
  & | & \textbf{print\_locales}
  \end{tabular}
  \end{small}
  \vspace{2ex}
  \hrule
  \caption{Locales extend the grammar of Isar.}
  \label{fig-grammar}
  \end{figure}

  At the theory level --- that is, at the outer syntactic level of an
  Isabelle input file --- \textbf{locale} declares a named
  locale.  Other kinds of locales,
  locale expressions and unnamed locales, will be introduced later.  When
  declaring a named locale, it is possible to \emph{import} another
  named locale, or indeed several ones by importing a locale
  expression.  The second part of the declaration, also optional,
  consists of a number of context element declarations.  Here, a fifth
  kind, \textbf{includes}, is available.

  A number of Isar commands have an additional, optional \emph{target}
  argument, which always refers to a named locale.  These commands
  are \textbf{theorem} (together with \textbf{lemma} and
  \textbf{corollary}),  \textbf{theorems} (and
  \textbf{lemmas}), and \textbf{declare}.  The effect of specifying a target is
  that these commands focus on the specified locale, not the
  surrounding theory.  Commands that are used to
  prove new theorems will add them not to the theory, but to the
  locale.  Similarly, \textbf{declare} modifies attributes of theorems
  that belong to the specified target.  Additionally, for
  \textbf{theorem} (and related commands), theorems stored in the target
  can be used in the associated proof scripts.

  The Locales package permits a \emph{long goals format} for
  propositions stated with \textbf{theorem} (and friends).  While
  normally a goal is just a formula, a long goal is a list of context
  elements, followed by the keyword \textbf{shows}, followed by the
  formula.  Roughly speaking, the context elements are
  (additional) premises.  For an example, see
  Section~\ref{sec-includes}.  The list of context elements in a long goal
  is also called \emph{unnamed locale}.

  Finally, there are two commands to inspect locales when working in
  interactive mode: \textbf{print\_locales} prints the names of all
  targets
  visible in the current theory, \textbf{print\_locale} outputs the
  elements of a named locale or locale expression.

  The following presentation will use notation of
  Isabelle's meta logic, hence a few sentences to explain this.
  The logical
  primitives are universal quantification (@{text "\<And>"}), entailment
  (@{text "\<Longrightarrow>"}) and equality (@{text "\<equiv>"}).  Variables (not bound
  variables) are sometimes preceded by a question mark.  The logic is
  typed.  Type variables are denoted by @{text "'a"}, @{text "'b"}
  etc., and @{text "\<Rightarrow>"} is the function type.  Double brackets @{text
  "\<lbrakk>"} and @{text "\<rbrakk>"} are used to abbreviate nested entailment.
*}

subsection {* Parameters, Assumptions and Facts *}

text {*
  From a logical point of view a \emph{context} is a formula schema of
  the form
\[
  @{text "\<And>x\<^sub>1\<dots>x\<^sub>n. \<lbrakk> C\<^sub>1; \<dots> ;C\<^sub>m \<rbrakk> \<Longrightarrow> \<dots>"}
\]
  The variables $@{text "x\<^sub>1"}, \ldots, @{text "x\<^sub>n"}$ are
  called \emph{parameters}, the premises $@{text "C\<^sub>1"}, \ldots,
  @{text "C\<^sub>n"}$ \emph{assumptions}.  A formula @{text "F"}
  holds in this context if
\begin{equation}
\label{eq-fact-in-context}
  @{text "\<And>x\<^sub>1\<dots>x\<^sub>n. \<lbrakk> C\<^sub>1; \<dots> ;C\<^sub>m \<rbrakk> \<Longrightarrow> F"}
\end{equation}
  is valid.  The formula is called a \emph{fact} of the context.

  A locale allows fixing the parameters @{text
  "x\<^sub>1, \<dots>, x\<^sub>n"} and making the assumptions @{text
  "C\<^sub>1, \<dots>, C\<^sub>m"}.  This implicitly builds the context in
  which the formula @{text "F"} can be established.
  Parameters of a locale correspond to the context element
  \textbf{fixes}, and assumptions may be declared with
  \textbf{assumes}.  Using these context elements one can define
  the specification of semigroups.
*}

locale semi =
  fixes prod :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<cdot>" 70)
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

text {*
  The parameter @{term prod} has a
  syntax annotation allowing the infix ``@{text "\<cdot>"}'' in the
  assumption of associativity.  Parameters may have arbitrary mixfix
  syntax, like constants.  In the example, the type of @{term prod} is
  specified explicitly.  This is not necessary.  If no type is
  specified, a most general type is inferred simultaneously for all
  parameters, taking into account all assumptions (and type
  specifications of parameters, if present).%
\footnote{Type inference also takes into account definitions and
  import, as introduced later.}

  Free variables in assumptions are implicitly universally quantified,
  unless they are parameters.  Hence the context defined by the locale
  @{term "semi"} is
\[
  @{text "\<And>prod. \<lbrakk> \<And>x y z. prod (prod x y) z = prod x (prod y z)
  \<rbrakk> \<Longrightarrow> \<dots>"}
\]
  The locale can be extended to commutative semigroups.
*}

locale comm_semi = semi +
  assumes comm: "x \<cdot> y = y \<cdot> x"

text {*
  This locale \emph{imports} all elements of @{term "semi"}.  The
  latter locale is called the import of @{term "comm_semi"}. The
  definition adds commutativity, hence its context is
\begin{align*%
}
  @{text "\<And>prod. \<lbrakk> "} & 
  @{text "\<And>x y z. prod (prod x y) z = prod x (prod y z);"} \\
  & @{text "\<And>x y. prod x y = prod y x \<rbrakk> \<Longrightarrow> \<dots>"}
\end{align*%
}
  One may now derive facts --- for example, left-commutativity --- in
  the context of @{term "comm_semi"} by specifying this locale as
  target, and by referring to the names of the assumptions @{text
  assoc} and @{text comm} in the proof.
*}

theorem (in comm_semi) lcomm:
  "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" by (simp add: assoc)
  also have "\<dots> = (y \<cdot> x) \<cdot> z" by (simp add: comm)
  also have "\<dots> = y \<cdot> (x \<cdot> z)" by (simp add: assoc)
  finally show ?thesis .
qed

text {*
  In this equational Isar proof, ``@{text "\<dots>"}'' refers to the
  right hand side of the preceding equation.
  After the proof is finished, the fact @{text "lcomm"} is added to
  the locale @{term "comm_semi"}.  This is done by adding a
  \textbf{notes} element to the internal representation of the locale,
  as explained the next section.
*}

subsection {* Locale Predicates and the Internal Representation of
  Locales *}

text {*
\label{sec-locale-predicates}
  In mathematical texts, often arbitrary but fixed objects with
  certain properties are considered --- for instance, an arbitrary but
  fixed group $G$ --- with the purpose of establishing facts valid for
  any group.  These facts are subsequently used on other objects that
  also have these properties.

  Locales permit the same style of reasoning.  Exporting a fact $F$
  generalises the fixed parameters and leads to a (valid) formula of the
  form of equation~(\ref{eq-fact-in-context}).  If a locale has many
  assumptions
  (possibly accumulated through a number of imports) this formula can
  become large and cumbersome.  Therefore, Wenzel introduced 
  predicates that abbreviate the assumptions of locales.  These
  predicates are not confined to the locale but are visible in the
  surrounding theory.

  The definition of the locale @{term semi} generates the \emph{locale
  predicate} @{term semi} over the type of the parameter @{term prod},
  hence the predicate's type is @{typ "(['a, 'a] \<Rightarrow> 'a)
  \<Rightarrow> bool"}.  Its
  definition is
\begin{equation}
  \tag*{@{thm [source] semi_def}:} @{thm semi_def}.
\end{equation}
  In the case where the locale has no import, the generated
  predicate abbreviates all assumptions and is over the parameters
  that occur in these assumptions.

  The situation is more complicated when a locale extends
  another locale, as is the case for @{term comm_semi}.  Two
  predicates are defined.  The predicate
  @{term comm_semi_axioms} corresponds to the new assumptions and is
  called \emph{delta predicate}, the locale
  predicate @{term comm_semi} captures the content of all the locale,
  including the import.
  If a locale has neither assumptions nor import, no predicate is
  defined.  If a locale has import but no assumptions, only the locale
  predicate is defined.
*}
(*<*)
ML_setup {*
  val [comm_semi_ax1, comm_semi_ax2] = thms "comm_semi.axioms";
  bind_thm ("comm_semi_ax1", comm_semi_ax1);
  bind_thm ("comm_semi_ax2", comm_semi_ax2);
*}
(*>*)
text {*
  The Locales package generates a number of theorems for locale and
  delta predicates.  All predicates have a definition and an
  introduction rule.  Locale predicates that are defined in terms of
  other predicates (which is the case if and only if the locale has
  import) also have a number of elimination rules (called
  \emph{axioms}).  All generated theorems for the predicates of the
  locales @{text semi} and @{text comm_semi} are shown in
  Figures~\ref{fig-theorems-semi} and~\ref{fig-theorems-comm-semi},
  respectively.
  \begin{figure}
  \hrule
  \vspace{2ex}
  Theorems generated for the predicate @{term semi}.
  \begin{gather}
    \tag*{@{thm [source] semi_def}:} @{thm semi_def} \\
    \tag*{@{thm [source] semi.intro}:} @{thm semi.intro}
  \end{gather}
  \hrule
  \caption{Theorems for the locale predicate @{term "semi"}.}
  \label{fig-theorems-semi}
  \end{figure}

  \begin{figure}[h]
  \hrule
  \vspace{2ex}
  Theorems generated for the predicate @{term "comm_semi_axioms"}.
  \begin{gather}
    \tag*{@{thm [source] comm_semi_axioms_def}:} @{thm
    comm_semi_axioms_def} \\                        
    \tag*{@{thm [source] comm_semi_axioms.intro}:} @{thm
    comm_semi_axioms.intro}                       
  \end{gather}
  Theorems generated for the predicate @{term "comm_semi"}.
  \begin{gather}
    \tag*{@{thm [source] comm_semi_def}:} @{thm
    comm_semi_def} \\                          
    \tag*{@{thm [source] comm_semi.intro}:} @{thm
    comm_semi.intro} \\
    \tag*{@{thm [source] comm_semi.axioms}:} \mbox{} \\
    \notag @{thm comm_semi_ax1} \\
    \notag @{thm comm_semi_ax2}               
  \end{gather} 
  \hrule
  \caption{Theorems for the predicates @{term "comm_semi_axioms"} and
    @{term "comm_semi"}.}
  \label{fig-theorems-comm-semi}
  \end{figure}
  Note that the theorems generated by a locale
  definition may be inspected immediately after the definition in the
  Proof General interface \cite{Aspinall2000} of Isabelle through
  the menu item ``Isabelle/Isar$>$Show me $\ldots>$Theorems''.

  Locale and delta predicates are used also in the internal
  representation of locales as lists of context elements.  While all
  \textbf{fixes} in a
  declaration generate internal \textbf{fixes}, all assumptions
  of one locale declaration contribute to one internal \textbf{assumes}
  element.  The internal representation of @{term semi} is
\[
\begin{array}{ll}
  \textbf{fixes} & @{text prod} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"}
    (\textbf{infixl} @{text [quotes] "\<cdot>"} 70) \\
  \textbf{assumes} & @{text [quotes] "semi prod"} \\
  \textbf{notes} & @{text assoc}: @{text [quotes] "?x \<cdot> ?y \<cdot> ?z = ?x \<cdot> (?y \<cdot>
    ?z)"}
\end{array}
\]
  and the internal representation of @{text [quotes] comm_semi} is
\begin{equation}
\label{eq-comm-semi}
\begin{array}{ll}
  \textbf{fixes} & @{text prod} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"}
    ~(\textbf{infixl}~@{text [quotes] "\<cdot>"}~70) \\
  \textbf{assumes} & @{text [quotes] "semi prod"} \\
  \textbf{notes} & @{text assoc}: @{text [quotes] "?x \<cdot> ?y \<cdot> ?z = ?x \<cdot> (?y \<cdot>
    ?z)"} \\
  \textbf{assumes} & @{text [quotes] "comm_semi_axioms prod"} \\
  \textbf{notes} & @{text comm}: @{text [quotes] "?x \<cdot> ?y = ?y \<cdot> ?x"} \\
  \textbf{notes} & @{text lcomm}: @{text [quotes] "?x \<cdot> (?y \<cdot> ?z) = ?y \<cdot> (?x \<cdot>
    ?z)"}
\end{array}
\end{equation}
  The \textbf{notes} elements store facts of the
  locales.  The facts @{text assoc} and @{text comm} were added
  during the declaration of the locales.  They stem from assumptions,
  which are trivially facts.  The fact @{text lcomm} was
  added later, after finishing the proof in the respective
  \textbf{theorem} command above.

  By using \textbf{notes} in a declaration, facts can be added
  to a locale directly.  Of course, these must be theorems.
  Typical use of this feature includes adding theorems that are not
  usually used as a default rewrite rules by the simplifier to the
  simpset of the locale by a \textbf{notes} element with the attribute
  @{text "[simp]"}.  This way it is also possible to add specialised
  versions of
  theorems to a locale by instantiating locale parameters for unknowns
  or locale assumptions for premises.
*}

subsection {* Definitions *}

text {*
  Definitions were available in Kamm\"uller's version of Locales, and
  they are in Wenzel's.  
  The context element \textbf{defines} adds a definition of the form
  @{text "p x\<^sub>1 \<dots> x\<^sub>n \<equiv> t"} as an assumption, where @{term p} is a
  parameter of the locale (possibly an imported parameter), and @{text
  t} a term that may contain the @{text "x\<^sub>i"}.  The parameter may
  neither occur in a previous \textbf{assumes} or \textbf{defines}
  element, nor on the right hand side of the definition.  Hence
  recursion is not allowed.
  The parameter may, however, occur in subsequent \textbf{assumes} and
  on the right hand side of subsequent \textbf{defines}.  We call
  @{term p} \emph{defined parameter}.
*}

locale semi2 = semi +
  fixes rprod (infixl "\<odot>" 70)
  defines rprod_def: "rprod x y \<equiv> y \<cdot> x "

text {*
  This locale extends @{term semi} by a second binary operation @{text
  [quotes] \<odot>} that is like @{text [quotes] \<cdot>} but with
  reversed arguments.  The
  definition of the locale generates the predicate @{term semi2},
  which is equivalent to @{text semi}, but no @{term "semi2_axioms"}.
  The difference between \textbf{assumes} and \textbf{defines} lies in
  the way parameters are treated on export.
*}

subsection {* Export *}

text {*
  A fact is exported out
  of a locale by generalising over the parameters and adding
  assumptions as premises.  For brevity of the exported theorems,
  locale predicates are used.  Exported facts are referenced by
  writing qualified names consisting of the locale name and the fact name ---
  for example,
\begin{equation}
  \tag*{@{thm [source] semi.assoc}:} @{thm semi.assoc}.
\end{equation}
  Defined parameters receive special treatment.  Instead of adding a
  premise for the definition, the definition is unfolded in the
  exported theorem.  In order to illustrate this we prove that the
  reverse operation @{text [quotes] \<odot>} defined in the locale
  @{text semi2} is also associative.
*}

theorem (in semi2) r_assoc: "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  by (simp only: rprod_def assoc)                                    

text {*
  The exported fact is
\begin{equation}
  \tag*{@{thm [source] semi2.r_assoc}:} @{thm semi2.r_assoc}.
\end{equation}
  The defined parameter is not present but is replaced by its
  definition.  Note that the definition itself is not exported, hence
  there is no @{text "semi2.rprod_def"}.%
\footnote{The definition could alternatively be exported using a
  let-construct if there was one in Isabelle's meta-logic.  Let is
  usually defined in object-logics.}
*}

section {* Locale Expressions *}

text {*
  Locale expressions provide a simple language for combining
  locales.  They are an effective means of building complex
  specifications from simple ones.  Locale expressions are the main
  innovation of the version of Locales discussed here.  Locale
  expressions are also reason for introducing locale predicates.
*}

subsection {* Rename and Merge *}

text {*
  The grammar of locale expressions is part of the grammar in
  Figure~\ref{fig-grammar}.  Locale names are locale
  expressions, and
  further expressions are obtained by \emph{rename} and \emph{merge}.
\begin{description}
\item[Rename.]
  The locale expression $e\: q_1 \ldots q_n$ denotes
  the locale of $e$ where pa\-ra\-me\-ters, in the order in
  which they are fixed, are renamed to $q_1$ to $q_n$.
  The expression is only well-formed if $n$ does not
  exceed the number of parameters of $e$.  Underscores denote
  parameters that are not renamed.
  Parameters whose names are changed lose mixfix syntax,
  and there is currently no way to re-equip them with such.
\item[Merge.]
  The locale expression $e_1 + e_2$ denotes
  the locale obtained by merging the locales of $e_1$
  and $e_2$.  This locale contains the context elements
  of $e_1$, followed by the context elements of $e_2$.

  In actual fact, the semantics of the merge operation
  is more complicated.  If $e_1$ and $e_2$ are expressions containing
  the same name, followed by
  identical parameter lists, then the merge of both will contain
  the elements of those locales only once.  Details are explained in
  Section~\ref{sec-normal-forms} below.

  The merge operation is associative but not commutative.  The latter
  is because parameters of $e_1$ appear
  before parameters of $e_2$ in the composite expression.
\end{description}

  Rename can be used if a different parameter name seems more
  appropriate --- for example, when moving from groups to rings, a
  parameter @{text G} representing the group could be changed to
  @{text R}.  Besides of this stylistic use, renaming is important in
  combination with merge.  Both operations are used in the following
  specification of semigroup homomorphisms.
*}

locale semi_hom = comm_semi sum + comm_semi +
  fixes hom
  assumes hom: "hom (sum x y) = hom x \<cdot> hom y"

text {*
  This locale defines a context with three parameters @{text "sum"},
  @{text "prod"} and @{text "hom"}.  Only the second parameter has
  mixfix syntax.  The first two are associative operations,
  the first of type @{typ "['a, 'a] \<Rightarrow> 'a"}, the second of
  type @{typ "['b, 'b] \<Rightarrow> 'b"}.  

  How are facts that are imported via a locale expression identified?
  Facts are always introduced in a named locale (either in the
  locale's declaration, or by using the locale as target in
  \textbf{theorem}), and their names are
  qualified by the parameter names of this locale.
  Hence the full name of associativity in @{text "semi"} is
  @{text "prod.assoc"}.  Renaming parameters of a target also renames
  the qualifier of facts.  Hence, associativity of @{text "sum"} is
  @{text "sum.assoc"}.  Several parameters are separated by
  underscores in qualifiers.  For example, the full name of the fact
  @{text "hom"} in the locale @{text "semi_hom"} is @{text
  "sum_prod_hom.hom"}.

  The following example is quite artificial, it illustrates the use of
  facts, though.
*}

theorem (in semi_hom) "hom x \<cdot> (hom y \<cdot> hom z) = hom (sum x (sum y z))"
proof -
  have "hom x \<cdot> (hom y \<cdot> hom z) = hom y \<cdot> (hom x \<cdot> hom z)"
    by (simp add: prod.lcomm)
  also have "\<dots> = hom (sum y (sum x z))" by (simp add: hom)
  also have "\<dots> = hom (sum x (sum y z))" by (simp add: sum.lcomm)
  finally show ?thesis .
qed

text {*
  Importing via a locale expression imports all facts of
  the imported locales, hence both @{text "sum.lcomm"} and @{text
  "prod.lcomm"} are
  available in @{text "hom_semi"}.  The import is dynamic --- that is,
  whenever facts are added to a locale, they automatically
  become available in subsequent \textbf{theorem} commands that use
  the locale as a target, or a locale importing the locale.
*}

subsection {* Normal Forms *}

text_raw {*
\label{sec-normal-forms}
\newcommand{\I}{\mathcal{I}}
\newcommand{\F}{\mathcal{F}}
\newcommand{\N}{\mathcal{N}}
\newcommand{\C}{\mathcal{C}}
\newcommand{\App}{\mathbin{\overline{@}}}
*}

text {*
  Locale expressions are interpreted in a two-step process.  First, an
  expression is normalised, then it is converted to a list of context
  elements.

  Normal forms are based on \textbf{locale} declarations.  These
  consist of an import section followed by a list of context
  elements.  Let $\I(l)$ denote the locale expression imported by
  locale $l$.  If $l$ has no import then $\I(l) = \varepsilon$.
  Likewise, let $\F(l)$ denote the list of context elements, also
  called the \emph{context fragment} of $l$.  Note that $\F(l)$
  contains only those context elements that are stated in the
  declaration of $l$, not imported ones.

\paragraph{Example 1.}  Consider the locales @{text semi} and @{text
  "comm_semi"}.  We have $\I(@{text semi}) = \varepsilon$ and
  $\I(@{text "comm_semi"}) = @{text semi}$, and the context fragments
  are
\begin{align*%
}
  \F(@{text semi}) & = \left[
\begin{array}{ll}
  \textbf{fixes} & @{text prod} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"}
    ~(\textbf{infixl}~@{text [quotes] "\<cdot>"}~70) \\
  \textbf{assumes} & @{text [quotes] "semi prod"} \\
  \textbf{notes} & @{text assoc}: @{text  [quotes]"?x \<cdot> ?y \<cdot> ?z = ?x \<cdot> (?y \<cdot>
    ?z)"}
\end{array} \right], \\
  \F(@{text "comm_semi"}) & = \left[
\begin{array}{ll}
  \textbf{assumes} & @{text [quotes] "comm_semi_axioms prod"} \\
  \textbf{notes} & @{text comm}: @{text [quotes] "?x \<cdot> ?y = ?y \<cdot> ?x"} \\
  \textbf{notes} & @{text lcomm}: @{text [quotes] "?x \<cdot> (?y \<cdot> ?z) = ?y \<cdot> (?x \<cdot>
    ?z)"}
\end{array} \right].
\end{align*%
}
  Let $\pi_0(\F(l))$ denote the list of parameters defined in the
  \textbf{fixes} elements of $\F(l)$ in the order of their occurrence.
  The list of parameters of a locale expression $\pi(e)$ is defined as
  follows:
\begin{align*%
}
  \pi(l) & = \pi(\I(l)) \App \pi_0(\F(l)) \text{, for named locale $l$.} \\
  \pi(e\: q_1 \ldots q_n) & = \text{$[q_1, \ldots, q_n, p_{n+1}, \ldots,
    p_{m}]$, where $\pi(e) = [p_1, \ldots, p_m]$.} \\
  \pi(e_1 + e_2) & = \pi(e_1) \App \pi(e_2)
\end{align*%
}
  The operation $\App$ concatenates two lists but omits elements from
  the second list that are also present in the first list.
  It is not possible to rename more parameters than there
  are present in an expression --- that is, $n \le m$ --- otherwise
  the renaming is illegal.  If $q_i
  = \_$ then the $i$th entry of the resulting list is $p_i$.

  In the normalisation phase, imports of named locales are unfolded, and
  renames and merges are recursively propagated to the imported locale
  expressions.  The result is a list of locale names, each with a full
  list of parameters, where locale names occurring with the same parameter
  list twice are removed.  Let $\N$ denote normalisation.  It is defined
  by these equations:
\begin{align*%
}
  \N(l) & = \N(\I(l)) \App [l\:\pi(l)] \text{, for named locale $l$.} \\
  \N(e\: q_1 \ldots q_n) & = \N(e)\:[q_1 \ldots q_n/\pi(e)] \\
  \N(e_1 + e_2) & = \N(e_1) \App \N(e_2)
\end{align*%
}
  Normalisation yields a list of \emph{identifiers}.  An identifier
  consists of a locale name and a (possibly empty) list of parameters.

  In the second phase, the list of identifiers $\N(e)$ is converted to
  a list of context elements $\C(e)$ by converting each identifier to
  a list of context elements, and flattening the obtained list.
  Conversion of the identifier $l\:q_1 \ldots q_n$ yields the list of
  context elements $\F(l)$, but with the following modifications:
\begin{itemize}
\item
  Rename the parameter in the $i$th \textbf{fixes} element of $\F(l)$
  to $q_i$, $i = 1, \ldots, n$.  If the parameter name is actually
  changed then delete the syntax annotation.  Renaming a parameter may
  also change its type.
\item
  Perform the same renamings on all occurrences of parameters (fixed
  variables) in \textbf{assumes}, \textbf{defines} and \textbf{notes}
  elements.
\item
  Qualify names of facts by $q_1\_\ldots\_q_n$.
\end{itemize}
  The locale expression is \emph{well-formed} if it contains no
  illegal renamings and the following conditions on $\C(e)$ hold,
  otherwise the expression is rejected:
\begin{itemize}
\item Parameters in \textbf{fixes} are distinct;
\item Free variables in \textbf{assumes} and
  \textbf{defines} occur in preceding \textbf{fixes};%
\footnote{This restriction is relaxed for contexts obtained with
  \textbf{includes}, see Section~\ref{sec-includes}.}
\item Parameters defined in \textbf{defines} must neither occur in
  preceding \textbf{assumes} nor \textbf{defines}.
\end{itemize}
*}

subsection {* Examples *}

text {*
\paragraph{Example 2.}
  We obtain the context fragment $\C(@{text "comm_semi"})$ of the
  locale @{text "comm_semi"}.  First, the parameters are computed.
\begin{align*%
}
  \pi(@{text "semi"}) & = [@{text prod}] \\
  \pi(@{text "comm_semi"}) & = \pi(@{text "semi"}) \App []
     = [@{text prod}]
\end{align*%
}
  Next, the normal form of the locale expression
  @{text "comm_semi"} is obtained.
\begin{align*%
}
  \N(@{text "semi"}) & = [@{text semi} @{text prod}] \\
  \N(@{text "comm_semi"}) & = \N(@{text "semi"}) \App
       [@{text "comm_semi prod"}]
   = [@{text "semi prod"}, @{text "comm_semi prod"}]
\end{align*%
}
  Converting this to a list of context elements leads to the
  list~(\ref{eq-comm-semi}) shown in
  Section~\ref{sec-locale-predicates}, but with fact names qualified
  by @{text prod} --- for example, @{text "prod.assoc"}.
  Qualification was omitted to keep the presentation simple.
  Isabelle's scoping rules identify the most recent fact with
  qualified name $x.a$ when a fact with name $a$ is requested.

\paragraph{Example 3.}
  The locale expression @{text "comm_semi sum"} involves
  renaming.  Computing parameters yields $\pi(@{text "comm_semi sum"})
  = [@{text sum}]$, the normal form is
\begin{align*%
}
  \N(@{text "comm_semi sum"}) & =
  \N(@{text "comm_semi"})[@{text sum}/@{text prod}] =
  [@{text "semi sum"}, @{text "comm_semi sum"}]
\end{align*%
}
  and the list of context elements
\[
\begin{array}{ll}
  \textbf{fixes} & @{text sum} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"} \\
  \textbf{assumes} & @{text [quotes] "semi sum"} \\
  \textbf{notes} & @{text sum.assoc}: @{text [quotes] "sum (sum ?x ?y) ?z
    = sum ?x (sum ?y ?z)"} \\
  \textbf{assumes} & @{text [quotes] "comm_semi_axioms sum"} \\
  \textbf{notes} & @{text sum.comm}: @{text [quotes] "sum ?x ?y = sum
    ?y ?x"} \\
  \textbf{notes} & @{text sum.lcomm}: @{text [quotes] "sum ?x (sum ?y ?z)
    = sum ?y (sum ?x ?z)"}
\end{array}
\]

\paragraph{Example 4.}
  The context defined by the locale @{text "semi_hom"} involves
  merging two copies of @{text "comm_semi"}.  We obtain the parameter
  list and normal form:
\begin{align*%
}
  \pi(@{text "semi_hom"}) & = \pi(@{text "comm_semi sum"} +
       @{text "comm_semi"}) \App [@{text hom}] \\
     & = (\pi(@{text "comm_semi sum"}) \App \pi(@{text "comm_semi"}))
       \App [@{text hom}] \\
     & = ([@{text sum}] \App [@{text prod}]) \App [@{text hom}]
     = [@{text sum}, @{text prod}, @{text hom}] \\
  \N(@{text "semi_hom"}) & =
       \N(@{text "comm_semi sum"} + @{text "comm_semi"}) \App \\
     & \phantom{==}
       [@{text "semi_hom sum prod hom"}] \\
     & = (\N(@{text "comm_semi sum"}) \App \N(@{text "comm_semi"})) \App \\
     & \phantom{==}
       [@{text "semi_hom sum prod hom"}] \\
     & = ([@{text "semi sum"}, @{text "comm_semi sum"}] \App %\\
%     & \phantom{==}
       [@{text "semi prod"}, @{text "comm_semi prod"}]) \App \\
     & \phantom{==}
       [@{text "semi_hom sum prod hom"}] \\
     & = [@{text "semi sum"}, @{text "comm_semi sum"},
       @{text "semi prod"}, @{text "comm_semi prod"}, \\
     & \phantom{==}
       @{text "semi_hom sum prod hom"}].
\end{align*%
}
  Hence $\C(@{text "semi_hom"})$, shown below, is again well-formed.
\[
\begin{array}{ll}
  \textbf{fixes} & @{text sum} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"} \\
  \textbf{assumes} & @{text [quotes] "semi sum"} \\
  \textbf{notes} & @{text sum.assoc}: @{text [quotes] "sum (sum ?x ?y) ?z
    = sum ?x (sum ?y ?z)"} \\
  \textbf{assumes} & @{text [quotes] "comm_semi_axioms sum"} \\
  \textbf{notes} & @{text sum.comm}: @{text [quotes] "sum ?x ?y = sum ?y ?x"} \\
  \textbf{notes} & @{text sum.lcomm}: @{text [quotes] "sum ?x (sum ?y ?z)
    = sum ?y (sum ?x ?z)"} \\
  \textbf{fixes} & @{text prod} :: @{typ [quotes] "['b, 'b] \<Rightarrow> 'b"}
    ~(\textbf{infixl}~@{text [quotes] "\<cdot>"}~70) \\
  \textbf{assumes} & @{text [quotes] "semi prod"} \\
  \textbf{notes} & @{text prod.assoc}: @{text [quotes] "?x \<cdot> ?y \<cdot> ?z = ?x \<cdot> (?y \<cdot>
    ?z)"} \\
  \textbf{assumes} & @{text [quotes] "comm_semi_axioms prod"} \\
  \textbf{notes} & @{text prod.comm}: @{text [quotes] "?x \<cdot> ?y = ?y \<cdot> ?x"} \\
  \textbf{notes} & @{text prod.lcomm}: @{text [quotes] "?x \<cdot> (?y \<cdot> ?z) = ?y \<cdot> (?x \<cdot>
    ?z)"} \\
  \textbf{fixes} & @{text hom} :: @{typ [quotes] "'a \<Rightarrow> 'b"} \\
  \textbf{assumes} & @{text [quotes] "semi_hom_axioms sum"} \\
  \textbf{notes} & @{text "sum_prod_hom.hom"}:
    @{text "hom (sum x y) = hom x \<cdot> hom y"}
\end{array}
\]

\paragraph{Example 5.}
  In this example, a locale expression leading to a list of context
  elements that is not well-defined is encountered, and it is illustrated
  how normalisation deals with multiple inheritance.
  Consider the specification of monads (in the algebraic sense)
  and monoids.
*}

locale monad =
  fixes prod :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<cdot>" 70) and one :: 'a ("\<one>" 100)
  assumes l_one: "\<one> \<cdot> x = x" and r_one: "x \<cdot> \<one> = x"

text {*
  Monoids are both semigroups and monads and one would want to
  specify them as locale expression @{text "semi + monad"}.
  Unfortunately, this expression is not well-formed.  Its normal form
\begin{align*%
}
  \N(@{text "monad"}) & = [@{text "monad prod"}] \\
  \N(@{text "semi"}+@{text "monad"}) & =
       \N(@{text "semi"}) \App \N(@{text "monad"})
     = [@{text "semi prod"}, @{text "monad prod"}]
\end{align*%
}
  leads to a list containing the context element
\[
  \textbf{fixes}~@{text prod} :: @{typ [quotes] "['a, 'a] \<Rightarrow> 'a"}
    ~(\textbf{infixl}~@{text [quotes] "\<cdot>"}~70)
\]
  twice and thus violating the first criterion of well-formedness.  To
  avoid this problem, one can
  introduce a new locale @{text magma} with the sole purpose of fixing the
  parameter and defining its syntax.  The specifications of semigroup
  and monad are changed so that they import @{text magma}.
*}

locale magma = fixes prod (infixl "\<cdot>" 70)

locale semi' = magma + assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
locale monad' = magma + fixes one ("\<one>" 100)
  assumes l_one: "\<one> \<cdot> x = x" and r_one: "x \<cdot> \<one> = x"

text {*
  Normalisation now yields
\begin{align*%
}
  \N(@{text "semi' + monad'"}) & =
       \N(@{text "semi'"}) \App \N(@{text "monad'"}) \\
     & = (\N(@{text magma}) \App [@{text "semi' prod"}]) \App
         (\N(@{text magma}) \App [@{text "monad' prod"}]) \\
     & = [@{text "magma prod"}, @{text "semi' prod"}] \App
         [@{text "magma prod"}, @{text "monad' prod"}]) \\
     & = [@{text "magma prod"}, @{text "semi' prod"},
          @{text "monad' prod"}]
\end{align*%
}
  where the second occurrence of @{text "magma prod"} is eliminated.
  The reader is encouraged to check, using the \textbf{print\_locale}
  command, that the list of context elements generated from this is
  indeed well-formed.

  It follows that importing
  parameters is more flexible than fixing them using a context element.
  The Locale package provides the predefined locale @{term var} that
  can be used to import parameters if no
  particular mixfix syntax is required.
  Its definition is
\begin{center}
  \textbf{locale} \textit{var} = \textbf{fixes} @{text "x_"}
\end{center}
   The use of the internal variable @{text "x_"}
  enforces that the parameter is renamed before being used, because
  internal variables may not occur in the input syntax.
*}

subsection {* Includes *}

text {*
\label{sec-includes}
  The context element \textbf{includes} takes a locale expression $e$
  as argument.  It can occur at any point in a locale declaration, and
  it adds $\C(e)$ to the current context.

  If \textbf{includes} $e$ appears as context element in the
  declaration of a named locale $l$, the included context is only
  visible in subsequent context elements, but it is not propagated to
  $l$.  That is, if $l$ is later used as a target, context elements
  from $\C(e)$ are not added to the context.  Although it is
  conceivable that this mechanism could be used to add only selected
  facts from $e$ to $l$ (with \textbf{notes} elements following
  \textbf{includes} $e$), currently no useful applications of this are
  known.

  The more common use of \textbf{includes} $e$ is in long goals, where it
  adds, like a target, locale context to the proof context.  Unlike
  with targets, the proved theorem is not stored
  in the locale.  Instead, it is exported immediately.
*}

theorem lcomm2:
  includes comm_semi shows "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" by (simp add: assoc)
  also have "\<dots> = (y \<cdot> x) \<cdot> z" by (simp add: comm)
  also have "\<dots> = y \<cdot> (x \<cdot> z)" by (simp add: assoc)
  finally show ?thesis .
qed

text {*
  This proof is identical to the proof of @{text lcomm}.  The use of
  \textbf{includes} provides the same context and facts as when using
  @{term comm_semi} as target.  On the other hand, @{thm [source]
  lcomm2} is not added as a fact to the locale @{term comm_semi}, but
  is directly visible in the theory.  The theorem is
\[
  @{thm lcomm2}.
\]
  Note that it is possible to
  combine a target and (several) \textbf{includes} in a goal statement, thus
  using contexts of several locales but storing the theorem in only
  one of them.
*}

section {* Structures *}

text {*
\label{sec-structures}
  The specifications of semigroups and monoids that served as examples
  in previous sections modelled each operation of an algebraic
  structure as a single parameter.  This is rather inconvenient for
  structures with many operations, and also unnatural.  In accordance
  to mathematical texts, one would rather fix two groups instead of
  two sets of operations.

  The approach taken in Isabelle is to encode algebraic structures
  with suitable types (in Isabelle/HOL usually records).  An issue to
  be addressed by
  locales is syntax for algebraic structures.  This is the purpose of
  the \textbf{(structure)} annotation in \textbf{fixes}, introduced by
  Wenzel.  We illustrate this, independently of record types, with a
  different formalisation of semigroups.

  Let @{text "'a semi_type"} be a not further specified type that
  represents semigroups over the carrier type @{typ "'a"}.  Let @{text
  "s_op"} be an operation that maps an object of @{text "'a semi_type"} to
  a binary operation.
*}

typedecl 'a semi_type
consts s_op :: "['a semi_type, 'a, 'a] \<Rightarrow> 'a" (infixl "\<star>\<index>" 70)

text {*
  Although @{text "s_op"} is a ternary operation, it is declared
  infix.  The syntax annotation contains the token  @{text \<index>}
  (\verb.\<index>.), which refers to the first argument.  This syntax is only
  effective in the context of a locale, and only if the first argument
  is a
  \emph{structural} parameter --- that is, a parameter with annotation
  \textbf{(structure)}.  The token has the effect of replacing the
  parameter with a subscripted number, the index of the structural
  parameter in the locale.  This replacement takes place both for
  printing and
  parsing.  Subscripted $1$ for the first structural
  parameter may be omitted, as in this specification of semigroups with
  structures:
*}

locale comm_semi' =
  fixes G :: "'a semi_type" (structure)
  assumes assoc: "(x \<star> y) \<star> z = x \<star> (y \<star> z)" and comm: "x \<star> y = y \<star> x"

text {*
  Here @{text "x \<star> y"} is equivalent to @{text "x \<star>\<^sub>1 y"} and
  abbreviates @{term "s_op G x y"}.  A specification of homomorphisms
  requires a second structural parameter.
*}

locale semi'_hom = comm_semi' + comm_semi' H +
  fixes hom
  assumes hom: "hom (x \<star> y) = hom x \<star>\<^sub>2 hom y"

text {*
  The parameter @{text H} is defined in the second \textbf{fixes}
  element of $\C(@{term "semi'_comm"})$. Hence @{text "\<star>\<^sub>2"}
  abbreviates @{term "s_op H x y"}.  The same construction can be done
  with records instead of an \textit{ad-hoc} type.  In general, the
  $i$th structural parameter is addressed by index $i$.  Only the
  index $1$ may be omitted.  *}

record 'a semi = prod :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<bullet>\<index>" 70)

text {*
  This declares the types @{typ "'a semi"} and  @{typ "('a, 'b)
  semi_scheme"}.  The latter is an extensible record, where the second
  type argument is the type of the extension field.  For details on
  records, see \cite{NipkowEtAl2002} Chapter~8.3.
*}

locale semi_w_records = struct G +
  assumes assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"

text {*
  The type @{typ "('a, 'b) semi_scheme"} is inferred for the parameter @{term
  G}.  Using subtyping on records, the specification can be extended
  to groups easily.
*}

record 'a group = "'a semi" +
  one :: "'a" ("l\<index>" 100)
  inv :: "'a \<Rightarrow> 'a" ("inv\<index> _" [81] 80)
locale group_w_records = semi_w_records +
  assumes l_one: "l \<bullet> x = x" and l_inv: "inv x \<bullet> x = l"

text {*
 Finally, the predefined locale
\begin{center}
  \textbf{locale} \textit{struct} = \textbf{fixes} @{text "S_"}
    \textbf{(structure)}.
\end{center}
  is analogous to @{text "var"}.  
  More examples on the use of structures, including groups, rings and
  polynomials can be found in the Isabelle distribution in the
  session HOL-Algebra.
*}

section {* Conclusions and Outlook *}

text {*
  Locales provide a simple means of modular reasoning.  They allow to
  abbreviate frequently occurring context statements and maintain facts
  valid in these contexts.  Importantly, using structures, they allow syntax to be
  effective only in certain contexts, and thus to mimic common
  practice in mathematics, where notation is chosen very flexibly.
  This is also known as literate formalisation \cite{Bailey1998}.
  Locale expressions allow to duplicate and merge
  specifications.  This is a necessity, for example, when reasoning about
  homomorphisms.  Normalisation makes it possible to deal with
  diamond-shaped inheritance structures, and generally with directed
  acyclic graphs.  The combination of locales with record
  types in higher-order logic provides an effective means for
  specifying algebraic structures: locale import and record subtyping
  provide independent hierarchies for specifications and structure
  elements.  Rich examples for this can be found in
  the Isabelle distribution in the session HOL-Algebra.

  The primary reason for writing this report was to provide a better
  understanding of locales in Isar.  Wenzel provided hardly any
  documentation, with the exception of \cite{Wenzel2002b}.  The
  present report should make it easier for users of Isabelle to take
  advantage of locales.

  The report is also a base for future extensions.  These include
  improved syntax for structures.  Identifying them by numbers seems
  unnatural and can be confusing if more than two structures are
  involved --- for example, when reasoning about universal
  properties --- and numbering them by order of occurrence seems
  arbitrary.  Another desirable feature is \emph{instantiation}.  One
  may, in the course of a theory development, construct objects that
  fulfil the specification of a locale.  These objects are possibly
  defined in the context of another locale.  Instantiation should make it
  simple to specialise abstract facts for the object under
  consideration and to use the specified facts.

  A detailed comparison of locales with module systems in type theory
  has not been undertaken yet, but could be beneficial.  For example,
  a module system for Coq has recently been presented by Chrzaszcz
  \cite{Chrzaszcz2003}.  While the
  latter usually constitute extensions of the calculus, locales are
  a rather thin layer that does not change Isabelle's meta logic.
  Locales mainly manage specifications and facts.  Functors, like
  the constructor for polynomial rings, remain objects of the
  logic.

  \textbf{Acknowledgements.}  Lawrence C.\ Paulson and Norbert
  Schirmer made useful comments on a draft of this paper.
*}
                                
(*<*)
end
(*>*)