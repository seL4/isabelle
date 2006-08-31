
(* $Id$ *)

theory prelim imports base begin

chapter {* Preliminaries *}

section {* Contexts \label{sec:context} *}

text {*
  A logical context represents the background that is taken for
  granted when formulating statements and composing proofs.  It acts
  as a medium to produce formal content, depending on earlier material
  (declarations, results etc.).

  In particular, derivations within the primitive Pure logic can be
  described as a judgment @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}, meaning that a
  proposition @{text "\<phi>"} is derivable from hypotheses @{text "\<Gamma>"}
  within the theory @{text "\<Theta>"}.  There are logical reasons for
  keeping @{text "\<Theta>"} and @{text "\<Gamma>"} separate: theories support type
  constructors and schematic polymorphism of constants and axioms,
  while the inner calculus of @{text "\<Gamma> \<turnstile> \<phi>"} is limited to Simple
  Type Theory (with fixed type variables in the assumptions).

  \medskip Contexts and derivations are linked by the following key
  principles:

  \begin{itemize}

  \item Transfer: monotonicity of derivations admits results to be
  transferred into a larger context, i.e.\ @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}
  implies @{text "\<Gamma>' \<turnstile>\<^sub>\<Theta>\<^sub>' \<phi>"} for contexts @{text "\<Theta>' \<supseteq>
  \<Theta>"} and @{text "\<Gamma>' \<supseteq> \<Gamma>"}.

  \item Export: discharge of hypotheses admits results to be exported
  into a smaller context, i.e.\ @{text "\<Gamma>' \<turnstile>\<^sub>\<Theta> \<phi>"} implies
  @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<Delta> \<Longrightarrow> \<phi>"} where @{text "\<Gamma>' \<supseteq> \<Gamma>"} and @{text "\<Delta> =
  \<Gamma>' - \<Gamma>"}.  Note that @{text "\<Theta>"} remains unchanged here, only the
  @{text "\<Gamma>"} part is affected.

  \end{itemize}

  \medskip Isabelle/Isar provides two different notions of abstract
  containers called \emph{theory context} and \emph{proof context},
  respectively.  These model the main characteristics of the primitive
  @{text "\<Theta>"} and @{text "\<Gamma>"} above, without subscribing to any
  particular kind of content yet.  Instead, contexts merely impose a
  certain policy of managing arbitrary \emph{context data}.  The
  system provides strongly typed mechanisms to declare new kinds of
  data at compile time.

  Thus the internal bootstrap process of Isabelle/Pure eventually
  reaches a stage where certain data slots provide the logical content
  of @{text "\<Theta>"} and @{text "\<Gamma>"} sketched above, but this does not
  stop there!  Various additional data slots support all kinds of
  mechanisms that are not necessarily part of the core logic.

  For example, there would be data for canonical introduction and
  elimination rules for arbitrary operators (depending on the
  object-logic and application), which enables users to perform
  standard proof steps implicitly (cf.\ the @{text "rule"} method).

  Isabelle is able to bring forth more and more concepts successively.
  In particular, an object-logic like Isabelle/HOL continues the
  Isabelle/Pure setup by adding specific components for automated
  reasoning (classical reasoner, tableau prover, structured induction
  etc.) and derived specification mechanisms (inductive predicates,
  recursive functions etc.).  All of this is based on the generic data
  management by theory and proof contexts.
*}


subsection {* Theory context \label{sec:context-theory} *}

text {*
  \glossary{Theory}{FIXME}

  Each theory is explicitly named and holds a unique identifier.
  There is a separate \emph{theory reference} for pointing backwards
  to the enclosing theory context of derived entities.  Theories are
  related by a (nominal) sub-theory relation, which corresponds to the
  canonical dependency graph: each theory is derived from a certain
  sub-graph of ancestor theories.  The @{text "merge"} of two theories
  refers to the least upper bound, which actually degenerates into
  absorption of one theory into the other, due to the nominal
  sub-theory relation this.

  The @{text "begin"} operation starts a new theory by importing
  several parent theories and entering a special @{text "draft"} mode,
  which is sustained until the final @{text "end"} operation.  A draft
  mode theory acts like a linear type, where updates invalidate
  earlier drafts, but theory reference values will be propagated
  automatically.  Thus derived entities that ``belong'' to a draft
  might be transferred spontaneously to a larger context.  An
  invalidated draft is called ``stale''.

  The @{text "checkpoint"} operation produces an intermediate stepping
  stone that will survive the next update unscathed: both the original
  and the changed theory remain valid and are related by the
  sub-theory relation.  Checkpointing essentially recovers purely
  functional theory values, at the expense of some extra internal
  bookeeping.

  The @{text "copy"} operation produces an auxiliary version that has
  the same data content, but is unrelated to the original: updates of
  the copy do not affect the original, neither does the sub-theory
  relation hold.

  \medskip The example in \figref{fig:ex-theory} below shows a theory
  graph derived from @{text "Pure"}. Theory @{text "Length"} imports
  @{text "Nat"} and @{text "List"}.  The theory body consists of a
  sequence of updates, working mostly on drafts.  Intermediate
  checkpoints may occur as well, due to the history mechanism provided
  by the Isar toplevel, cf.\ \secref{sec:isar-toplevel}.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{rcccl}
        &            & @{text "Pure"} \\
        &            & @{text "\<down>"} \\
        &            & @{text "FOL"} \\
        & $\swarrow$ &              & $\searrow$ & \\
  $Nat$ &            &              &            & @{text "List"} \\
        & $\searrow$ &              & $\swarrow$ \\
        &            & @{text "Length"} \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{imports}$} \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{begin}$} \\
        &            & $\vdots$~~ \\
        &            & @{text "\<bullet>"}~~ \\
        &            & $\vdots$~~ \\
        &            & @{text "\<bullet>"}~~ \\
        &            & $\vdots$~~ \\
        &            & \multicolumn{3}{l}{~~$\isarkeyword{end}$} \\
  \end{tabular}
  \caption{Theory definition depending on ancestors}\label{fig:ex-theory}
  \end{center}
  \end{figure}
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type theory} \\
  @{index_ML Theory.subthy: "theory * theory -> bool"} \\
  @{index_ML Theory.merge: "theory * theory -> theory"} \\
  @{index_ML Theory.checkpoint: "theory -> theory"} \\
  @{index_ML Theory.copy: "theory -> theory"} \\[1ex]
  @{index_ML_type theory_ref} \\
  @{index_ML Theory.self_ref: "theory -> theory_ref"} \\
  @{index_ML Theory.deref: "theory_ref -> theory"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type theory} represents theory contexts.  This is a
  linear type!  Most operations destroy the old version, which then
  becomes ``stale''.

  \item @{ML "Theory.subthy"}~@{text "(thy\<^sub>1, thy\<^sub>2)"}
  compares theories according to the inherent graph structure of the
  construction.  This sub-theory relation is a nominal approximation
  of inclusion (@{text "\<subseteq>"}) of the corresponding content.

  \item @{ML "Theory.merge"}~@{text "(thy\<^sub>1, thy\<^sub>2)"}
  absorbs one theory into the other.  This fails for unrelated
  theories!

  \item @{ML "Theory.checkpoint"}~@{text "thy"} produces a safe
  stepping stone in the linear development of @{text "thy"}.  The next
  update will result in two related, valid theories.

  \item @{ML "Theory.copy"}~@{text "thy"} produces a variant of @{text
  "thy"} that holds a copy of the same data.  The copy is not related
  to the original, which is not touched at all.

  \item @{ML_type theory_ref} represents a sliding reference to a
  valid theory --- updates on the original are propagated
  automatically.

  \item @{ML "Theory.self_ref"} and @{ML "Theory.deref"} convert
  between @{ML_type "theory"} and @{ML_type "theory_ref"}.  As the
  referenced theory evolves monotonically over time, later invocations
  of @{ML "Theory.deref"} may refer to larger contexts.

  \end{description}
*}


subsection {* Proof context \label{sec:context-proof} *}

text {*
  \glossary{Proof context}{The static context of a structured proof,
  acts like a local ``theory'' of the current portion of Isar proof
  text, generalizes the idea of local hypotheses @{text "\<Gamma>"} in
  judgments @{text "\<Gamma> \<turnstile> \<phi>"} of natural deduction calculi.  There is a
  generic notion of introducing and discharging hypotheses.
  Arbritrary auxiliary context data may be adjoined.}

  A proof context is a container for pure data with a back-reference
  to the theory it belongs to.  Modifications to draft theories are
  propagated automatically as usual, but there is also an explicit
  @{text "transfer"} operation to resynchronize with more substantial
  updates to the underlying theory.  The actual context data does not
  require any special bookkeeping, thanks to the lack of destructive
  features.

  Entities derived in a proof context need to record inherent logical
  requirements explicitly, since there is no separate context
  identification as for theories.  For example, hypotheses used in
  primitive derivations (cf.\ \secref{sec:thm}) are recorded
  separately within the sequent @{text "\<Gamma> \<turnstile> \<phi>"}, just to make double
  sure.  Results could still leak into an alien proof context do to
  programming errors, but Isabelle/Isar includes some extra validity
  checks in critical positions, notably at the end of sub-proof.

  Proof contexts may be produced in arbitrary ways, although the
  common discipline is to follow block structure as a mental model: a
  given context is extended consecutively, and results are exported
  back into the original context.  Note that the Isar proof states
  model block-structured reasoning explicitly, using a stack of proof
  contexts, cf.\ \secref{isar-proof-state}.
*}

text %mlref {* FIXME *}


subsection {* Generic contexts *}

text FIXME

text %mlref {* FIXME *}


subsection {* Context data *}

text {*
*}


section {* Named entities *}

text {* Named entities of different kinds (logical constant, type,
type class, theorem, method etc.) live in separate name spaces.  It is
usually clear from the occurrence of a name which kind of entity it
refers to.  For example, proof method @{text "foo"} vs.\ theorem
@{text "foo"} vs.\ logical constant @{text "foo"} are easily
distinguished by means of the syntactic context.  A notable exception
are logical identifiers within a term (\secref{sec:terms}): constants,
fixed variables, and bound variables all share the same identifier
syntax, but are distinguished by their scope.

Each name space is organized as a collection of \emph{qualified
names}, which consist of a sequence of basic name components separated
by dots: @{text "Bar.bar.foo"}, @{text "Bar.foo"}, and @{text "foo"}
are examples for valid qualified names.  Name components are
subdivided into \emph{symbols}, which constitute the smallest textual
unit in Isabelle --- raw characters are normally not encountered
directly. *}


subsection {* Strings of symbols *}

text {* Isabelle strings consist of a sequence of
symbols\glossary{Symbol}{The smalles unit of text in Isabelle,
subsumes plain ASCII characters as well as an infinite collection of
named symbols (for greek, math etc.).}, which are either packed as an
actual @{text "string"}, or represented as a list.  Each symbol is in
itself a small string of the following form:

\begin{enumerate}

\item either a singleton ASCII character ``@{text "c"}'' (with
character code 0--127), for example ``\verb,a,'',

\item or a regular symbol ``\verb,\,\verb,<,@{text "ident"}\verb,>,'',
for example ``\verb,\,\verb,<alpha>,'',

\item or a control symbol ``\verb,\,\verb,<^,@{text
"ident"}\verb,>,'', for example ``\verb,\,\verb,<^bold>,'',

\item or a raw control symbol ``\verb,\,\verb,<^raw:,@{text
"\<dots>"}\verb,>,'' where ``@{text "\<dots>"}'' refers to any
printable ASCII character (excluding ``\verb,.,'' and ``\verb,>,'') or
non-ASCII character, for example ``\verb,\,\verb,<^raw:$\sum_{i = 1}^n$>,'',

\item or a numbered raw control symbol ``\verb,\,\verb,<^raw,@{text
"nnn"}\verb,>, where @{text "nnn"} are digits, for example
``\verb,\,\verb,<^raw42>,''.

\end{enumerate}

The @{text "ident"} syntax for symbol names is @{text "letter (letter
| digit)\<^sup>*"}, where @{text "letter = A..Za..Z"} and @{text
"digit = 0..9"}.  There are infinitely many regular symbols and
control symbols available, but a certain collection of standard
symbols is treated specifically.  For example,
``\verb,\,\verb,<alpha>,'' is classified as a (non-ASCII) letter,
which means it may occur within regular Isabelle identifier syntax.

Output of symbols depends on the print mode (\secref{sec:print-mode}).
For example, the standard {\LaTeX} setup of the Isabelle document
preparation system would present ``\verb,\,\verb,<alpha>,'' as @{text
"\<alpha>"}, and ``\verb,\,\verb,<^bold>,\verb,\,\verb,<alpha>,'' as @{text
"\<^bold>\<alpha>"}.

\medskip It is important to note that the character set underlying
Isabelle symbols is plain 7-bit ASCII.  Since 8-bit characters are
passed through transparently, Isabelle may easily process actual
Unicode/UCS data (using the well-known UTF-8 encoding, for example).
Unicode provides its own collection of mathematical symbols, but there
is presently no link to Isabelle's named ones; both kinds of symbols
coexist independently. *}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type "Symbol.symbol"} \\
  @{index_ML Symbol.explode: "string -> Symbol.symbol list"} \\
  @{index_ML Symbol.is_letter: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_digit: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_quasi: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_blank: "Symbol.symbol -> bool"} \\
  @{index_ML_type "Symbol.sym"} \\
  @{index_ML Symbol.decode: "Symbol.symbol -> Symbol.sym"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type "Symbol.symbol"} represents Isabelle symbols; this type
  is merely an alias for @{ML_type "string"}, but emphasizes the
  specific format encountered here.

  \item @{ML "Symbol.explode"}~@{text "s"} produces a symbol list from
  the packed form usually encountered as user input.  This function
  replaces @{ML "String.explode"} for virtually all purposes of
  manipulating text in Isabelle!  Plain @{ML "implode"} may be used
  for the reverse operation.

  \item @{ML "Symbol.is_letter"}, @{ML "Symbol.is_digit"}, @{ML
  "Symbol.is_quasi"}, @{ML "Symbol.is_blank"} classify certain symbols
  (both ASCII and several named ones) according to fixed syntactic
  convections of Isabelle, e.g.\ see \cite{isabelle-isar-ref}.

  \item @{ML_type "Symbol.sym"} is a concrete datatype that represents
  the different kinds of symbols explicitly as @{ML "Symbol.Char"},
  @{ML "Symbol.Sym"}, @{ML "Symbol.Ctrl"}, or @{ML "Symbol.Raw"}.

  \item @{ML "Symbol.decode"} converts the string representation of a
  symbol into the explicit datatype version.

  \end{description}
*}


subsection {* Qualified names and name spaces *}

text %FIXME {* Qualified names are constructed according to implicit naming
principles of the present context.


The last component is called \emph{base name}; the remaining prefix of
qualification may be empty.

Some practical conventions help to organize named entities more
systematically:

\begin{itemize}

\item Names are qualified first by the theory name, second by an
optional ``structure''.  For example, a constant @{text "c"} declared
as part of a certain structure @{text "b"} (say a type definition) in
theory @{text "A"} will be named @{text "A.b.c"} internally.

\item

\item

\item

\item

\end{itemize}

Names of different kinds of entities are basically independent, but
some practical naming conventions relate them to each other.  For
example, a constant @{text "foo"} may be accompanied with theorems
@{text "foo.intro"}, @{text "foo.elim"}, @{text "foo.simps"} etc.  The
same may happen for a type @{text "foo"}, which is then apt to cause
clashes in the theorem name space!  To avoid this, we occasionally
follow an additional convention of suffixes that determine the
original kind of entity that a name has been derived.  For example,
constant @{text "foo"} is associated with theorem @{text "foo.intro"},
type @{text "foo"} with theorem @{text "foo_type.intro"}, and type
class @{text "foo"} with @{text "foo_class.intro"}.

*}


section {* Structured output *}

subsection {* Pretty printing *}

text FIXME

subsection {* Output channels *}

text FIXME

subsection {* Print modes *}

text FIXME


end
