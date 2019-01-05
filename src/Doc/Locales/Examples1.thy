theory Examples1
imports Examples
begin

section \<open>Use of Locales in Theories and Proofs
  \label{sec:interpretation}\<close>

text \<open>
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

  As an example, consider the type of integers \<^typ>\<open>int\<close>.  The
  relation \<^term>\<open>(\<le>)\<close> is a total order over \<^typ>\<open>int\<close>.  We start
  with the interpretation that \<^term>\<open>(\<le>)\<close> is a partial order.  The
  facilities of the interpretation command are explored gradually in
  three versions.
\<close>


subsection \<open>First Version: Replacement of Parameters Only
  \label{sec:po-first}\<close>

text \<open>
  The command \isakeyword{interpretation} is for the interpretation of
  locale in theories.  In the following example, the parameter of locale
  \<open>partial_order\<close> is replaced by \<^term>\<open>(\<le>) :: int \<Rightarrow> int \<Rightarrow>
  bool\<close> and the locale instance is interpreted in the current
  theory.\<close>

  interpretation %visible int: partial_order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
txt \<open>\normalsize
  The argument of the command is a simple \emph{locale expression}
  consisting of the name of the interpreted locale, which is
  preceded by the qualifier \<open>int:\<close> and succeeded by a
  white-space-separated list of terms, which provide a full
  instantiation of the locale parameters.  The parameters are referred
  to by order of declaration, which is also the order in which
  \isakeyword{print\_locale} outputs them.  The locale has only a
  single parameter, hence the list of instantiation terms is a
  singleton.

  The command creates the goal
  @{subgoals [display]} which can be shown easily:
\<close>
    by unfold_locales auto

text \<open>The effect of the command is that instances of all
  conclusions of the locale are available in the theory, where names
  are prefixed by the qualifier.  For example, transitivity for \<^typ>\<open>int\<close> is named @{thm [source] int.trans} and is the following
  theorem:
  @{thm [display, indent=2] int.trans}
  It is not possible to reference this theorem simply as \<open>trans\<close>.  This prevents unwanted hiding of existing theorems of the
  theory by an interpretation.\<close>


subsection \<open>Second Version: Replacement of Definitions\<close>

text \<open>Not only does the above interpretation qualify theorem names.
  The prefix \<open>int\<close> is applied to all names introduced in locale
  conclusions including names introduced in definitions.  The
  qualified name \<open>int.less\<close> is short for
  the interpretation of the definition, which is \<open>partial_order.less (\<le>)\<close>.
  Qualified name and expanded form may be used almost
  interchangeably.%
\footnote{Since \<^term>\<open>(\<le>)\<close> is polymorphic, for \<open>partial_order.less (\<le>)\<close> a
  more general type will be inferred than for \<open>int.less\<close> which
  is over type \<^typ>\<open>int\<close>.}
  The former is preferred on output, as for example in the theorem
  @{thm [source] int.less_le_trans}: @{thm [display, indent=2]
  int.less_le_trans}
  Both notations for the strict order are not satisfactory.  The
  constant \<^term>\<open>(<)\<close> is the strict order for \<^typ>\<open>int\<close>.
  In order to allow for the desired replacement, interpretation
  accepts \emph{equations} in addition to the parameter instantiation.
  These follow the locale expression and are indicated with the
  keyword \isakeyword{rewrites}.  This is the revised interpretation:
\<close>
end
