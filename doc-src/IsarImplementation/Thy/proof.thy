
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

  \item @{ML Variable.declare_term} FIXME

  \item @{ML Variable.import} FIXME

  \item @{ML Variable.export} FIXME

  \item @{ML Variable.trade} composes @{ML Variable.import} and @{ML
  Variable.export}.

  \item @{ML Variable.monomorphic} FIXME

  \item @{ML Variable.polymorphic} FIXME

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
