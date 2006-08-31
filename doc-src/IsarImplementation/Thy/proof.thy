
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

text FIXME


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
