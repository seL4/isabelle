
(* $Id$ *)

theory logic imports base begin

chapter {* Pure logic *}

section {* Syntax *}

subsection {* Simply-typed lambda calculus *}

text {*

FIXME

\glossary{Type}{FIXME}
\glossary{Term}{FIXME}

*}

subsection {* The order-sorted algebra of types *}

text {*

FIXME

\glossary{Type constructor}{FIXME}

\glossary{Type class}{FIXME}

\glossary{Type arity}{FIXME}

\glossary{Sort}{FIXME}

*}


subsection {* Type-inference and schematic polymorphism *}

text {*

FIXME

\glossary{Schematic polymorphism}{FIXME}

\glossary{Type variable}{FIXME}

*}


section {* Theory *}

text {*

FIXME

\glossary{Constant}{Essentially a \seeglossary{fixed variable} of the
theory context, but slightly more flexible since it may be used at
different type-instances, due to \seeglossary{schematic
polymorphism.}}

*}


section {* Deduction *}

text {*

  FIXME

\glossary{Proposition}{A \seeglossary{term} of \seeglossary{type}
@{text "prop"}.  Internally, there is nothing special about
propositions apart from their type, but the concrete syntax enforces a
clear distinction.  Propositions are structured via implication @{text
"A \<Longrightarrow> B"} or universal quantification @{text "\<And>x. B x"} --- anything
else is considered atomic.  The canonical form for propositions is
that of a \seeglossary{Hereditary Harrop Formula}.}

\glossary{Theorem}{A proven proposition within a certain theory and
proof context, formally @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}; both contexts are
rarely spelled out explicitly.  Theorems are usually normalized
according to the \seeglossary{HHF} format.}

\glossary{Fact}{Sometimes used interchangably for
\seeglossary{theorem}.  Strictly speaking, a list of theorems,
essentially an extra-logical conjunction.  Facts emerge either as
local assumptions, or as results of local goal statements --- both may
be simultaneous, hence the list representation.}

\glossary{Schematic variable}{FIXME}

\glossary{Fixed variable}{A variable that is bound within a certain
proof context; an arbitrary-but-fixed entity within a portion of proof
text.}

\glossary{Free variable}{Synonymous for \seeglossary{fixed variable}.}

\glossary{Bound variable}{FIXME}

\glossary{Variable}{See \seeglossary{schematic variable},
\seeglossary{fixed variable}, \seeglossary{bound variable}, or
\seeglossary{type variable}.  The distinguishing feature of different
variables is their binding scope.}

*}

subsection {* Primitive inferences *}

text FIXME

subsection {* Higher-order resolution *}

text {*

FIXME

\glossary{Hereditary Harrop Formula}{The set of propositions in HHF
format is defined inductively as @{text "H = (\<And>x\<^sup>*. H\<^sup>* \<Longrightarrow>
A)"}, for variables @{text "x"} and atomic propositions @{text "A"}.
Any proposition may be put into HHF form by normalizing with the rule
@{text "(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)"}.  In Isabelle, the outermost
quantifier prefix is represented via \seeglossary{schematic
variables}, such that the top-level structure is merely that of a
\seeglossary{Horn Clause}}.

\glossary{HHF}{See \seeglossary{Hereditary Harrop Formula}.}

*}

subsection {* Equational reasoning *}

text FIXME


section {* Proof terms *}

text FIXME

end
