theory Examples1
imports Examples
begin

section {* Use of Locales in Theories and Proofs *}

text {* Locales enable to prove theorems abstractly, relative to
  sets of assumptions.  These theorems can then be used in other
  contexts where the assumptions themselves, or
  instances of the assumptions, are theorems.  This form of theorem
  reuse is called \emph{interpretation}.

  The changes of the locale
  hierarchy from the previous sections are examples of
  interpretations.  The command \isakeyword{sublocale} $l_1
  \subseteq l_2$ is said to \emph{interpret} locale $l_2$ in the
  context of $l_1$.  It causes all theorems of $l_2$ to be made
  available in $l_1$.  The interpretation is \emph{dynamic}: not only
  theorems already present in $l_2$ are available in $l_1$.  Theorems
  that will be added to $l_2$ in future will automatically be
  propagated to $l_1$.

  Locales can also be interpreted in the contexts of theories and
  structured proofs.  These interpretations are dynamic, too.
  Theorems added to locales will be propagated to theories.
  In this section the interpretation in
  theories is illustrated; interpretation in proofs is analogous.

  As an example, consider the type of natural numbers @{typ nat}.  The
  order relation @{text \<le>} is a total order over @{typ nat},
  divisibility @{text dvd} is a distributive lattice.  We start with the
  interpretation that @{text \<le>} is a partial order.  The facilities of
  the interpretation command are explored in three versions.
  *}


subsection {* First Version: Replacement of Parameters Only
  \label{sec:po-first} *}

text {*
  In the most basic form, interpretation just replaces the locale
  parameters by terms.  The following command interprets the locale
  @{text partial_order} in the global context of the theory.  The
  parameter @{term le} is replaced by @{term "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"}. *} 

  interpretation %visible nat: partial_order "op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool"
txt {* The locale name is succeeded by a \emph{parameter
  instantiation}.  This is a list of terms, which refer to
  the parameters in the order of declaration in the locale.  The
  locale name is preceded by an optional \emph{interpretation
  qualifier}.

  The command creates the goal%
\footnote{Note that @{text op} binds tighter than functions
  application: parentheses around @{text "op \<le>"} are not necessary.}
  @{subgoals [display]} which can be shown easily:
 *}
    by unfold_locales auto

text {*  Now theorems from the locale are available in the theory,
  interpreted for natural numbers, for example @{thm [source]
  nat.trans}: @{thm [display, indent=2] nat.trans}

  The interpretation qualifier, @{text nat} in the example, is applied
  to all names processed by the interpretation.  If a qualifer is
  given in the \isakeyword{interpretation} command, its use is
  mandatory when referencing the name.  For example, the above theorem
  cannot be referred to simply by @{text trans}.  This prevents
  unwanted hiding of theorems. *}


subsection {* Second Version: Replacement of Definitions *}

text {* The above interpretation also creates the theorem
  @{thm [source] nat.less_le_trans}: @{thm [display, indent=2]
  nat.less_le_trans}
  Here, @{term "partial_order.less (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool)"}
  represents the strict order, although @{text "<"} is the natural
  strict order for @{typ nat}.  Interpretation allows to map concepts
  introduced through definitions in locales to the corresponding
  concepts of the theory.%
\footnote{This applies not only to \isakeyword{definition} but also to
  \isakeyword{inductive}, \isakeyword{fun} and \isakeyword{function}.} 
  *}

end
