
(* $Id$ *)

theory "proof" imports base begin

chapter {* Structured reasoning *}

section {* Proof context *}

subsection {* Local variables *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Variable.declare_term: "term -> Proof.context -> Proof.context"} \\
  @{index_ML Variable.import: "bool -> thm list -> Proof.context -> thm list * Proof.context"} \\
  @{index_ML Variable.export: "Proof.context -> Proof.context -> thm list -> thm list"} \\
  @{index_ML Variable.trade: "Proof.context -> (thm list -> thm list) -> thm list -> thm list"} \\
  @{index_ML Variable.monomorphic: "Proof.context -> term list -> term list"} \\
  @{index_ML Variable.polymorphic: "Proof.context -> term list -> term list"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Variable.declare_term} declares a term as belonging to
  the current context.  This fixes free type variables, but not term
  variables; constraints for type and term variables are declared
  uniformly.

  \item @{ML Variable.import} introduces new fixes for schematic type
  and term variables occurring in given facts.  The effect may be
  reversed (up to renaming) via @{ML Variable.export}.

  \item @{ML Variable.export} generalizes fixed type and term
  variables according to the difference of the two contexts.  Note
  that type variables occurring in term variables are still fixed,
  even though they got introduced later (e.g.\ by type-inference).

  \item @{ML Variable.trade} composes @{ML Variable.import} and @{ML
  Variable.export}, i.e.\ it provides a view on facts with all
  variables being fixed in the current context.

  \item @{ML Variable.monomorphic} introduces fixed type variables for
  the schematic of the given facts.

  \item @{ML Variable.polymorphic} generalizes type variables as far
  as possible, even those occurring in fixed term variables.  This
  operation essentially reverses the default policy of type-inference
  to introduce local polymorphism entities in fixed form.

  \end{description}
*}

text FIXME

section {* Proof state *}

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

section {* Methods *}

text FIXME

section {* Attributes *}

text FIXME

end
