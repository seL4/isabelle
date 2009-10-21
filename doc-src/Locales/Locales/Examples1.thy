theory Examples1
imports Examples
begin
text {* \vspace{-5ex} *}
section {* Use of Locales in Theories and Proofs
  \label{sec:interpretation} *}

text {*
  Locales can be interpreted in the contexts of theories and
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

  As an example, consider the type of integers @{typ int}.  The
  relation @{term "op \<le>"} is a total order over @{typ int}.  We start
  with the interpretation that @{term "op \<le>"} is a partial order.  The
  facilities of the interpretation command are explored gradually in
  three versions.
  *}


subsection {* First Version: Replacement of Parameters Only
  \label{sec:po-first} *}

text {*
  The command \isakeyword{interpretation} is for the interpretation of
  locale in theories.  In the following example, the parameter of locale
  @{text partial_order} is replaced by @{term "op \<le> :: int \<Rightarrow> int \<Rightarrow>
  bool"} and the locale instance is interpreted in the current
  theory. *}

  interpretation %visible int: partial_order "op \<le> :: int \<Rightarrow> int \<Rightarrow> bool"
txt {* \normalsize
  The argument of the command is a simple \emph{locale expression}
  consisting of the name of the interpreted locale, which is
  preceded by the qualifier @{text "int:"} and succeeded by a
  white-space-separated list of terms, which provide a full
  instantiation of the locale parameters.  The parameters are referred
  to by order of declaration, which is also the order in which
  \isakeyword{print\_locale} outputs them.  The locale has only a
  single parameter, hence the list of instantiation terms is a
  singleton.

  The command creates the goal
  @{subgoals [display]} which can be shown easily:
 *}
    by unfold_locales auto

text {*  The effect of the command is that instances of all
  conclusions of the locale are available in the theory, where names
  are prefixed by the qualifier.  For example, transitivity for @{typ
  int} is named @{thm [source] int.trans} and is the following
  theorem:
  @{thm [display, indent=2] int.trans}
  It is not possible to reference this theorem simply as @{text
  trans}.  This prevents unwanted hiding of existing theorems of the
  theory by an interpretation. *}


subsection {* Second Version: Replacement of Definitions *}

text {* Not only does the above interpretation qualify theorem names.
  The prefix @{text int} is applied to all names introduced in locale
  conclusions including names introduced in definitions.  The
  qualified name @{text int.less} is short for
  the interpretation of the definition, which is @{term int.less}.
  Qualified name and expanded form may be used almost
  interchangeably.%
\footnote{Since @{term "op \<le>"} is polymorphic, for @{term int.less} a
  more general type will be inferred than for @{text int.less} which
  is over type @{typ int}.}
  The latter is preferred on output, as for example in the theorem
  @{thm [source] int.less_le_trans}: @{thm [display, indent=2]
  int.less_le_trans}
  Both notations for the strict order are not satisfactory.  The
  constant @{term "op <"} is the strict order for @{typ int}.
  In order to allow for the desired replacement, interpretation
  accepts \emph{equations} in addition to the parameter instantiation.
  These follow the locale expression and are indicated with the
  keyword \isakeyword{where}.  This is the revised interpretation:
  *}
end
