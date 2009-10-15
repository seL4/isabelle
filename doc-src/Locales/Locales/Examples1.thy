theory Examples1
imports Examples
begin

section {* Use of Locales in Theories and Proofs
  \label{sec:interpretation} *}

text {*
  Locales can also be interpreted in the contexts of theories and
  structured proofs.  These interpretations are dynamic, too.
  Conclusions of locales will be propagated to the current theory or
  the current proof context.%
\footnote{Strictly speaking, only interpretation in theories is
  dynamic since it is not possible to change locales or the locale
  hierarchy from within a proof.}
  The focus of this section is on
  interpretation in theories, but we will also encounter
  interpretations in proofs, in
  Section~\ref{sec:local-interpretation}.

  As an example, consider the type of natural numbers @{typ nat}.  The
  relation @{term "op \<le>"} is a total order over @{typ nat},
  divisibility @{text "op dvd"} forms a distributive lattice.  We start with the
  interpretation that @{term "op \<le>"} is a partial order.  The facilities of
  the interpretation command are explored gradually in three versions.
  *}


subsection {* First Version: Replacement of Parameters Only
  \label{sec:po-first} *}

text {*
  The command \isakeyword{interpretation} is for the interpretation of
  locale in theories.  In the following example, the parameter of locale
  @{text partial_order} is replaced by @{term "op \<le> :: nat \<Rightarrow> nat \<Rightarrow>
  bool"} and the locale instance is interpreted in the current
  theory. *}

  interpretation %visible nat: partial_order "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"
txt {* \normalsize
  The argument of the command is a simple \emph{locale expression}
  consisting of the name of the interpreted locale, which is
  preceded by the qualifier @{text "nat:"} and succeeded by a
  white-space-separated list of terms, which provide a full
  instantiation of the locale parameters.  The parameters are referred
  to by order of declaration, which is also the order in which
  \isakeyword{print\_locale} outputs them.

[TODO: Introduce morphisms.  Reference to \ref{sec:locale-expressions}.]

  The command creates the goal
  @{subgoals [display]} which can be shown easily:
 *}
    by unfold_locales auto

text {*  The effect of the command is that instances of all
  conclusions of the locale are available in the theory, where names
  are prefixed by the qualifier.  For example, transitivity for @{typ
  nat} is named @{thm [source] nat.trans} and is the following
  theorem:
  @{thm [display, indent=2] nat.trans}
  It is not possible to reference this theorem simply as @{text
  trans}, which prevents unwanted hiding of existing theorems of the
  theory by an interpretation. *}


subsection {* Second Version: Replacement of Definitions *}

text {* Not only does the above interpretation qualify theorem names.
  The prefix @{text nat} is applied to all names introduced in locale
  conclusions including names introduced in definitions.  The
  qualified name @{text nat.less} refers to
  the interpretation of the definition, which is @{term nat.less}.
  Qualified name and expanded form may be used almost
  interchangeably.%
\footnote{Since @{term "op \<le>"} is polymorphic, for @{term nat.less} a
  more general type will be inferred than for @{text nat.less} which
  is over type @{typ nat}.}
  The latter is preferred on output, as for example in the theorem
  @{thm [source] nat.less_le_trans}: @{thm [display, indent=2]
  nat.less_le_trans}
  Both notations for the strict order are not satisfactory.  The
  constant @{term "op <"} is the strict order for @{typ nat}.
  In order to allow for the desired replacement, interpretation
  accepts \emph{equations} in addition to the parameter instantiation.
  These follow the locale expression and are indicated with the
  keyword \isakeyword{where}.  The revised interpretation follows.
  *}
end
