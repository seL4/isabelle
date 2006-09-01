
(* $Id$ *)

theory "proof" imports base begin

chapter {* Structured proofs *}

section {* Variables and schematic polymorphism *}

text FIXME

text %mlref {*
  \begin{mldecls}
  @{index_ML Variable.declare_term: "term -> Proof.context -> Proof.context"} \\
  @{index_ML Variable.add_fixes: "string list -> Proof.context -> string list * Proof.context"} \\
  @{index_ML Variable.import: "bool -> thm list -> Proof.context -> ((ctyp list * cterm list) * thm list) * Proof.context"} \\
  @{index_ML Variable.export: "Proof.context -> Proof.context -> thm list -> thm list"} \\
  @{index_ML Variable.trade: "Proof.context -> (thm list -> thm list) -> thm list -> thm list"} \\
  @{index_ML Variable.polymorphic: "Proof.context -> term list -> term list"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Variable.declare_term}~@{text "t ctxt"} declares term
  @{text "t"} to belong to the context.  This fixes free type
  variables, but not term variables.  Constraints for type and term
  variables are declared uniformly.

  \item @{ML Variable.add_fixes}~@{text "xs ctxt"} fixes term
  variables @{text "xs"} and returns the internal names of the
  resulting Skolem constants.  Note that term fixes refer to
  \emph{all} type instances that may occur in the future.

  \item @{ML Variable.invent_fixes} is similar to @{ML
  Variable.add_fixes}, but the given names merely act as hints for
  internal fixes produced here.

  \item @{ML Variable.import}~@{text "open ths ctxt"} augments the
  context by new fixes for the schematic type and term variables
  occurring in @{text "ths"}.  The @{text "open"} flag indicates
  whether the fixed names should be accessible to the user, otherwise
  internal names are chosen.

  \item @{ML Variable.export}~@{text "inner outer ths"} generalizes
  fixed type and term variables in @{text "ths"} according to the
  difference of the @{text "inner"} and @{text "outer"} context.  Note
  that type variables occurring in term variables are still fixed.

  @{ML Variable.export} essentially reverses the effect of @{ML
  Variable.import} (up to renaming of schematic variables.

  \item @{ML Variable.trade} composes @{ML Variable.import} and @{ML
  Variable.export}, i.e.\ it provides a view on facts with all
  variables being fixed in the current context.

  \item @{ML Variable.polymorphic}~@{text "ctxt ts"} generalizes type
  variables in @{text "ts"} as far as possible, even those occurring
  in fixed term variables.  This operation essentially reverses the
  default policy of type-inference to introduce local polymorphism as
  fixed types.

  \end{description}
*}

text FIXME


section {* Assumptions *}

text {*
  An \emph{assumption} is a proposition that it is postulated in the
  current context.  Local conclusions may use assumptions as
  additional facts, but this imposes implicit hypotheses that weaken
  the overall statement.

  Assumptions are restricted to fixed non-schematic statements, all
  generality needs to be expressed by explicit quantifiers.
  Nevertheless, the result will be in HHF normal form with outermost
  quantifiers stripped.  For example, by assuming @{text "\<And>x :: \<alpha>. P
  x"} we get @{text "\<And>x :: \<alpha>. P x \<turnstile> P ?x"} for arbitrary @{text "?x"}
  of the fixed type @{text "\<alpha>"}.  Local derivations accumulate more
  and more explicit references to hypotheses: @{text "A\<^isub>1, \<dots>,
  A\<^isub>n \<turnstile> B"} where @{text "A\<^isub>1, \<dots>, A\<^isub>n"} needs to
  be covered by the assumptions of the current context.

  \medskip The @{text "add_assm"} operation augments the context by
  local assumptions, parameterized by an @{text "export"} rule (see
  below).

  The @{text "export"} operation moves facts from a (larger) inner
  context into a (smaller) outer context, by discharging the
  difference of the assumptions as specified by the associated export
  rules.  Note that the discharged portion is determined by the
  contexts, not the facts being exported!  There is a separate flag to
  indicate a goal context, where the result is meant to refine an
  enclosing sub-goal of a structured proof state (cf.\ FIXME).

  \medskip The most basic export rule discharges assumptions directly
  by means of the @{text "\<Longrightarrow>"} introduction rule:
  \[
  \infer[(@{text "\<Longrightarrow>_intro"})]{@{text "\<Gamma> \\ A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \]

  The variant for goal refinements marks the newly introduced
  premises, which causes the builtin goal refinement scheme of Isar to
  enforce unification with local premises within the goal:
  \[
  \infer[(@{text "#\<Longrightarrow>_intro"})]{@{text "\<Gamma> \\ A \<turnstile> #A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \]

  \medskip Alternative versions of assumptions may perform arbitrary
  transformations as long as a particular portion of hypotheses is
  removed from the given facts.

  For example, a local definition works by fixing @{text "x"} and
  assuming @{text "x \<equiv> t"}, with the following export rule to reverse
  the effect:
  \[
  \infer{@{text "\<Gamma> \\ x \<equiv> t \<turnstile> B t"}}{@{text "\<Gamma> \<turnstile> B x"}}
  \]

  \medskip The general concept supports block-structured reasoning
  nicely, with arbitrary mechanisms for introducing local assumptions.
  The common reasoning pattern is as follows:

  \medskip
  \begin{tabular}{l}
  @{text "add_assm e\<^isub>1 A\<^isub>1"} \\
  @{text "\<dots>"} \\
  @{text "add_assm e\<^isub>n A\<^isub>n"} \\
  @{text "export"} \\
  \end{tabular}
  \medskip

  \noindent The final @{text "export"} will turn any fact @{text
  "A\<^isub>1, \<dots>, A\<^isub>n \<turnstile> B"} into some @{text "\<turnstile> B'"}, by
  applying the export rules @{text "e\<^isub>1, \<dots>, e\<^isub>n"}
  inside-out.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Assumption.export} \\
  @{index_ML Assumption.assume: "cterm -> thm"} \\
  @{index_ML Assumption.add_assumes: "cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{index_ML Assumption.add_assms:
    "Assumption.export -> cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{index_ML Assumption.export: "bool -> Proof.context -> Proof.context -> thm -> thm"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Assumption.export}

  \item @{ML Assumption.assume}~@{text "A"} produces a raw assumption
  @{text "A \<turnstile> A'"}, where the conclusion @{text "A'"} is in HHF normal
  form.

  \item @{ML Assumption.add_assumes}~@{text "As"} augments the context
  by plain assumptions that are discharged via @{text "\<Longrightarrow>_intro"} or
  @{text "#\<Longrightarrow>_intro"}, depending on goal mode.  The resulting facts are
  hypothetical theorems as produced by @{ML Assumption.assume}.

  \item @{ML Assumption.add_assms}~@{text "e As"} augments the context
  by generic assumptions that are discharged via rule @{text "e"}.

  \item @{ML Assumption.export}~@{text "is_goal inner outer th"}
  exports result @{text "th"} from the the @{text "inner"} context
  back into the @{text "outer"} one.  The @{text "is_goal"} flag is
  @{text "true"} for goal mode.  The result is in HHF normal form.

  \end{description}
*}


section {* Conclusions *}

text FIXME


section {* Proof states \label{sec:isar-proof-state} *}

text {*
  FIXME

\glossary{Proof state}{The whole configuration of a structured proof,
consisting of a \seeglossary{proof context} and an optional
\seeglossary{structured goal}.  Internally, an Isar proof state is
organized as a stack to accomodate block structure of proof texts.
For historical reasons, a low-level \seeglossary{tactical goal} is
occasionally called ``proof state'' as well.}

\glossary{Structured goal}{FIXME}

\glossary{Goal}{See \seeglossary{tactical goal} or \seeglossary{structured goal}. \norefpage}


*}

section {* Proof methods *}

text FIXME

section {* Attributes *}

text "FIXME ?!"

end
