
(* $Id$ *)

theory prelim imports base begin

chapter {* Preliminaries *}

section {* Contexts \label{sec:context} *}

text {*
  A logical context represents the background that is required for
  formulating statements and composing proofs.  It acts as a medium to
  produce formal content, depending on earlier material (declarations,
  results etc.).

  For example, derivations within the Isabelle/Pure logic can be
  described as a judgment @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>"}, which means that a
  proposition @{text "\<phi>"} is derivable from hypotheses @{text "\<Gamma>"}
  within the theory @{text "\<Theta>"}.  There are logical reasons for
  keeping @{text "\<Theta>"} and @{text "\<Gamma>"} separate: theories can be
  liberal about supporting type constructors and schematic
  polymorphism of constants and axioms, while the inner calculus of
  @{text "\<Gamma> \<turnstile> \<phi>"} is strictly limited to Simple Type Theory (with
  fixed type variables in the assumptions).

  \medskip Contexts and derivations are linked by the following key
  principles:

  \begin{itemize}

  \item Transfer: monotonicity of derivations admits results to be
  transferred into a \emph{larger} context, i.e.\ @{text "\<Gamma> \<turnstile>\<^sub>\<Theta>
  \<phi>"} implies @{text "\<Gamma>' \<turnstile>\<^sub>\<Theta>\<^sub>' \<phi>"} for contexts @{text "\<Theta>'
  \<supseteq> \<Theta>"} and @{text "\<Gamma>' \<supseteq> \<Gamma>"}.

  \item Export: discharge of hypotheses admits results to be exported
  into a \emph{smaller} context, i.e.\ @{text "\<Gamma>' \<turnstile>\<^sub>\<Theta> \<phi>"}
  implies @{text "\<Gamma> \<turnstile>\<^sub>\<Theta> \<Delta> \<Longrightarrow> \<phi>"} where @{text "\<Gamma>' \<supseteq> \<Gamma>"} and
  @{text "\<Delta> = \<Gamma>' - \<Gamma>"}.  Note that @{text "\<Theta>"} remains unchanged here,
  only the @{text "\<Gamma>"} part is affected.

  \end{itemize}

  \medskip By modeling the main characteristics of the primitive
  @{text "\<Theta>"} and @{text "\<Gamma>"} above, and abstracting over any
  particular logical content, we arrive at the fundamental notions of
  \emph{theory context} and \emph{proof context} in Isabelle/Isar.
  These implement a certain policy to manage arbitrary \emph{context
  data}.  There is a strongly-typed mechanism to declare new kinds of
  data at compile time.

  The internal bootstrap process of Isabelle/Pure eventually reaches a
  stage where certain data slots provide the logical content of @{text
  "\<Theta>"} and @{text "\<Gamma>"} sketched above, but this does not stop there!
  Various additional data slots support all kinds of mechanisms that
  are not necessarily part of the core logic.

  For example, there would be data for canonical introduction and
  elimination rules for arbitrary operators (depending on the
  object-logic and application), which enables users to perform
  standard proof steps implicitly (cf.\ the @{text "rule"} method
  \cite{isabelle-isar-ref}).

  \medskip Thus Isabelle/Isar is able to bring forth more and more
  concepts successively.  In particular, an object-logic like
  Isabelle/HOL continues the Isabelle/Pure setup by adding specific
  components for automated reasoning (classical reasoner, tableau
  prover, structured induction etc.) and derived specification
  mechanisms (inductive predicates, recursive functions etc.).  All of
  this is ultimately based on the generic data management by theory
  and proof contexts introduced here.
*}


subsection {* Theory context \label{sec:context-theory} *}

text {*
  \glossary{Theory}{FIXME}

  A \emph{theory} is a data container with explicit named and unique
  identifier.  Theories are related by a (nominal) sub-theory
  relation, which corresponds to the dependency graph of the original
  construction; each theory is derived from a certain sub-graph of
  ancestor theories.

  The @{text "merge"} operation produces the least upper bound of two
  theories, which actually degenerates into absorption of one theory
  into the other (due to the nominal sub-theory relation).

  The @{text "begin"} operation starts a new theory by importing
  several parent theories and entering a special @{text "draft"} mode,
  which is sustained until the final @{text "end"} operation.  A draft
  theory acts like a linear type, where updates invalidate earlier
  versions.  An invalidated draft is called ``stale''.

  The @{text "checkpoint"} operation produces an intermediate stepping
  stone that will survive the next update: both the original and the
  changed theory remain valid and are related by the sub-theory
  relation.  Checkpointing essentially recovers purely functional
  theory values, at the expense of some extra internal bookkeeping.

  The @{text "copy"} operation produces an auxiliary version that has
  the same data content, but is unrelated to the original: updates of
  the copy do not affect the original, neither does the sub-theory
  relation hold.

  \medskip The example in \figref{fig:ex-theory} below shows a theory
  graph derived from @{text "Pure"}, with theory @{text "Length"}
  importing @{text "Nat"} and @{text "List"}.  The body of @{text
  "Length"} consists of a sequence of updates, working mostly on
  drafts.  Intermediate checkpoints may occur as well, due to the
  history mechanism provided by the Isar top-level, cf.\
  \secref{sec:isar-toplevel}.

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
  \caption{A theory definition depending on ancestors}\label{fig:ex-theory}
  \end{center}
  \end{figure}

  \medskip There is a separate notion of \emph{theory reference} for
  maintaining a live link to an evolving theory context: updates on
  drafts are propagated automatically.  The dynamic stops after an
  explicit @{text "end"} only.

  Derived entities may store a theory reference in order to indicate
  the context they belong to.  This implicitly assumes monotonic
  reasoning, because the referenced context may become larger without
  further notice.
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

  \item @{ML_type theory} represents theory contexts.  This is
  essentially a linear type!  Most operations destroy the original
  version, which then becomes ``stale''.

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
  "thy"} that holds a copy of the same data.  The result is not
  related to the original; the original is unchanched.

  \item @{ML_type theory_ref} represents a sliding reference to an
  always valid theory; updates on the original are propagated
  automatically.

  \item @{ML "Theory.self_ref"}~@{text "thy"} and @{ML
  "Theory.deref"}~@{text "thy_ref"} convert between @{ML_type
  "theory"} and @{ML_type "theory_ref"}.  As the referenced theory
  evolves monotonically over time, later invocations of @{ML
  "Theory.deref"} may refer to a larger context.

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
  to the theory it belongs to.  The @{text "init"} operation creates a
  proof context from a given theory.  Modifications to draft theories
  are propagated to the proof context as usual, but there is also an
  explicit @{text "transfer"} operation to force resynchronization
  with more substantial updates to the underlying theory.  The actual
  context data does not require any special bookkeeping, thanks to the
  lack of destructive features.

  Entities derived in a proof context need to record inherent logical
  requirements explicitly, since there is no separate context
  identification as for theories.  For example, hypotheses used in
  primitive derivations (cf.\ \secref{sec:thms}) are recorded
  separately within the sequent @{text "\<Gamma> \<turnstile> \<phi>"}, just to make double
  sure.  Results could still leak into an alien proof context do to
  programming errors, but Isabelle/Isar includes some extra validity
  checks in critical positions, notably at the end of sub-proof.

  Proof contexts may be manipulated arbitrarily, although the common
  discipline is to follow block structure as a mental model: a given
  context is extended consecutively, and results are exported back
  into the original context.  Note that the Isar proof states model
  block-structured reasoning explicitly, using a stack of proof
  contexts internally, cf.\ \secref{sec:isar-proof-state}.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Proof.context} \\
  @{index_ML ProofContext.init: "theory -> Proof.context"} \\
  @{index_ML ProofContext.theory_of: "Proof.context -> theory"} \\
  @{index_ML ProofContext.transfer: "theory -> Proof.context -> Proof.context"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Proof.context} represents proof contexts.  Elements
  of this type are essentially pure values, with a sliding reference
  to the background theory.

  \item @{ML ProofContext.init}~@{text "thy"} produces a proof context
  derived from @{text "thy"}, initializing all data.

  \item @{ML ProofContext.theory_of}~@{text "ctxt"} selects the
  background theory from @{text "ctxt"}, dereferencing its internal
  @{ML_type theory_ref}.

  \item @{ML ProofContext.transfer}~@{text "thy ctxt"} promotes the
  background theory of @{text "ctxt"} to the super theory @{text
  "thy"}.

  \end{description}
*}


subsection {* Generic contexts \label{sec:generic-context} *}

text {*
  A generic context is the disjoint sum of either a theory or proof
  context.  Occasionally, this enables uniform treatment of generic
  context data, typically extra-logical information.  Operations on
  generic contexts include the usual injections, partial selections,
  and combinators for lifting operations on either component of the
  disjoint sum.

  Moreover, there are total operations @{text "theory_of"} and @{text
  "proof_of"} to convert a generic context into either kind: a theory
  can always be selected from the sum, while a proof context might
  have to be constructed by an ad-hoc @{text "init"} operation.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Context.generic} \\
  @{index_ML Context.theory_of: "Context.generic -> theory"} \\
  @{index_ML Context.proof_of: "Context.generic -> Proof.context"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Context.generic} is the direct sum of @{ML_type
  "theory"} and @{ML_type "Proof.context"}, with the datatype
  constructors @{ML "Context.Theory"} and @{ML "Context.Proof"}.

  \item @{ML Context.theory_of}~@{text "context"} always produces a
  theory from the generic @{text "context"}, using @{ML
  "ProofContext.theory_of"} as required.

  \item @{ML Context.proof_of}~@{text "context"} always produces a
  proof context from the generic @{text "context"}, using @{ML
  "ProofContext.init"} as required (note that this re-initializes the
  context data with each invocation).

  \end{description}
*}

subsection {* Context data *}

text {*
  The main purpose of theory and proof contexts is to manage arbitrary
  data.  New data types can be declared incrementally at compile time.
  There are separate declaration mechanisms for any of the three kinds
  of contexts: theory, proof, generic.

  \paragraph{Theory data} may refer to destructive entities, which are
  maintained in direct correspondence to the linear evolution of
  theory values, including explicit copies.\footnote{Most existing
  instances of destructive theory data are merely historical relics
  (e.g.\ the destructive theorem storage, and destructive hints for
  the Simplifier and Classical rules).}  A theory data declaration
  needs to implement the following specification (depending on type
  @{text "T"}):

  \medskip
  \begin{tabular}{ll}
  @{text "name: string"} \\
  @{text "empty: T"} & initial value \\
  @{text "copy: T \<rightarrow> T"} & refresh impure data \\
  @{text "extend: T \<rightarrow> T"} & re-initialize on import \\
  @{text "merge: T \<times> T \<rightarrow> T"} & join on import \\
  @{text "print: T \<rightarrow> unit"} & diagnostic output \\
  \end{tabular}
  \medskip

  \noindent The @{text "name"} acts as a comment for diagnostic
  messages; @{text "copy"} is just the identity for pure data; @{text
  "extend"} is acts like a unitary version of @{text "merge"}, both
  should also include the functionality of @{text "copy"} for impure
  data.

  \paragraph{Proof context data} is purely functional.  A declaration
  needs to implement the following specification:

  \medskip
  \begin{tabular}{ll}
  @{text "name: string"} \\
  @{text "init: theory \<rightarrow> T"} & produce initial value \\
  @{text "print: T \<rightarrow> unit"} & diagnostic output \\
  \end{tabular}
  \medskip

  \noindent The @{text "init"} operation is supposed to produce a pure
  value from the given background theory.  The remainder is analogous
  to theory data.

  \paragraph{Generic data} provides a hybrid interface for both theory
  and proof data.  The declaration is essentially the same as for
  (pure) theory data, without @{text "copy"}, though.  The @{text
  "init"} operation for proof contexts merely selects the current data
  value from the background theory.

  \bigskip In any case, a data declaration of type @{text "T"} results
  in the following interface:

  \medskip
  \begin{tabular}{ll}
  @{text "init: theory \<rightarrow> theory"} \\
  @{text "get: context \<rightarrow> T"} \\
  @{text "put: T \<rightarrow> context \<rightarrow> context"} \\
  @{text "map: (T \<rightarrow> T) \<rightarrow> context \<rightarrow> context"} \\
  @{text "print: context \<rightarrow> unit"}
  \end{tabular}
  \medskip

  \noindent Here @{text "init"} needs to be applied to the current
  theory context once, in order to register the initial setup.  The
  other operations provide access for the particular kind of context
  (theory, proof, or generic context).  Note that this is a safe
  interface: there is no other way to access the corresponding data
  slot of a context.  By keeping these operations private, a component
  may maintain abstract values authentically, without other components
  interfering.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_functor TheoryDataFun} \\
  @{index_ML_functor ProofDataFun} \\
  @{index_ML_functor GenericDataFun} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_functor TheoryDataFun}@{text "(spec)"} declares data for
  type @{ML_type theory} according to the specification provided as
  argument structure.  The resulting structure provides data init and
  access operations as described above.

  \item @{ML_functor ProofDataFun}@{text "(spec)"} is analogous for
  type @{ML_type Proof.context}.

  \item @{ML_functor GenericDataFun}@{text "(spec)"} is analogous for
  type @{ML_type Context.generic}.

  \end{description}
*}


section {* Name spaces *}

text {*
  By general convention, each kind of formal entities (logical
  constant, type, type class, theorem, method etc.) lives in a
  separate name space.  It is usually clear from the syntactic context
  of a name, which kind of entity it refers to.  For example, proof
  method @{text "foo"} vs.\ theorem @{text "foo"} vs.\ logical
  constant @{text "foo"} are easily distinguished thanks to the design
  of the concrete outer syntax.  A notable exception are logical
  identifiers within a term (\secref{sec:terms}): constants, fixed
  variables, and bound variables all share the same identifier syntax,
  but are distinguished by their scope.

  Name spaces are organized uniformly, as a collection of qualified
  names consisting of a sequence of basic name components separated by
  dots: @{text "Bar.bar.foo"}, @{text "Bar.foo"}, and @{text "foo"}
  are examples for qualified names.

  Despite the independence of names of different kinds, certain naming
  conventions may relate them to each other.  For example, a constant
  @{text "foo"} could be accompanied with theorems @{text
  "foo.intro"}, @{text "foo.elim"}, @{text "foo.simps"} etc.  The same
  could happen for a type @{text "foo"}, but this is apt to cause
  clashes in the theorem name space!  To avoid this, there is an
  additional convention to add a suffix that determines the original
  kind.  For example, constant @{text "foo"} could associated with
  theorem @{text "foo.intro"}, type @{text "foo"} with theorem @{text
  "foo_type.intro"}, and type class @{text "foo"} with @{text
  "foo_class.intro"}.

  \medskip Name components are subdivided into \emph{symbols}, which
  constitute the smallest textual unit in Isabelle --- raw characters
  are normally not encountered.
*}


subsection {* Strings of symbols *}

text {*
  Isabelle strings consist of a sequence of
  symbols\glossary{Symbol}{The smallest unit of text in Isabelle,
  subsumes plain ASCII characters as well as an infinite collection of
  named symbols (for greek, math etc.).}, which are either packed as
  an actual @{text "string"}, or represented as a list.  Each symbol
  is in itself a small string of the following form:

  \begin{enumerate}

  \item either a singleton ASCII character ``@{text "c"}'' (with
  character code 0--127), for example ``\verb,a,'',

  \item or a regular symbol ``\verb,\,\verb,<,@{text
  "ident"}\verb,>,'', for example ``\verb,\,\verb,<alpha>,'',

  \item or a control symbol ``\verb,\,\verb,<^,@{text
  "ident"}\verb,>,'', for example ``\verb,\,\verb,<^bold>,'',

  \item or a raw control symbol ``\verb,\,\verb,<^raw:,@{text
  "\<dots>"}\verb,>,'' where ``@{text "\<dots>"}'' refers to any printable ASCII
  character (excluding ``\verb,.,'' and ``\verb,>,'') or non-ASCII
  character, for example ``\verb,\,\verb,<^raw:$\sum_{i = 1}^n$>,'',

  \item or a numbered raw control symbol ``\verb,\,\verb,<^raw,@{text
  "nnn"}\verb,>, where @{text "nnn"} are digits, for example
  ``\verb,\,\verb,<^raw42>,''.

  \end{enumerate}

  The @{text "ident"} syntax for symbol names is @{text "letter
  (letter | digit)\<^sup>*"}, where @{text "letter = A..Za..z"} and
  @{text "digit = 0..9"}.  There are infinitely many regular symbols
  and control symbols available, but a certain collection of standard
  symbols is treated specifically.  For example,
  ``\verb,\,\verb,<alpha>,'' is classified as a (non-ASCII) letter,
  which means it may occur within regular Isabelle identifier syntax.

  Output of symbols depends on the print mode
  (\secref{sec:print-mode}).  For example, the standard {\LaTeX} setup
  of the Isabelle document preparation system would present
  ``\verb,\,\verb,<alpha>,'' as @{text "\<alpha>"}, and
  ``\verb,\,\verb,<^bold>,\verb,\,\verb,<alpha>,'' as @{text
  "\<^bold>\<alpha>"}.

  \medskip It is important to note that the character set underlying
  Isabelle symbols is plain 7-bit ASCII.  Since 8-bit characters are
  passed through transparently, Isabelle may easily process
  Unicode/UCS data as well (using UTF-8 encoding).  Unicode provides
  its own collection of mathematical symbols, but there is no built-in
  link to the ones of Isabelle.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type "Symbol.symbol"} \\
  @{index_ML Symbol.explode: "string -> Symbol.symbol list"} \\
  @{index_ML Symbol.is_letter: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_digit: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_quasi: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_blank: "Symbol.symbol -> bool"} \\[1ex]
  @{index_ML_type "Symbol.sym"} \\
  @{index_ML Symbol.decode: "Symbol.symbol -> Symbol.sym"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type "Symbol.symbol"} represents Isabelle symbols.  This
  type is an alias for @{ML_type "string"}, but emphasizes the
  specific format encountered here.

  \item @{ML "Symbol.explode"}~@{text "s"} produces a symbol list from
  the packed form that is encountered in most practical situations.
  This function supercedes @{ML "String.explode"} for virtually all
  purposes of manipulating text in Isabelle!  Plain @{ML "implode"}
  may still be used for the reverse operation.

  \item @{ML "Symbol.is_letter"}, @{ML "Symbol.is_digit"}, @{ML
  "Symbol.is_quasi"}, @{ML "Symbol.is_blank"} classify certain symbols
  (both ASCII and several named ones) according to fixed syntactic
  conventions of Isabelle, cf.\ \cite{isabelle-isar-ref}.

  \item @{ML_type "Symbol.sym"} is a concrete datatype that represents
  the different kinds of symbols explicitly with constructors @{ML
  "Symbol.Char"}, @{ML "Symbol.Sym"}, @{ML "Symbol.Ctrl"}, or @{ML
  "Symbol.Raw"}.

  \item @{ML "Symbol.decode"} converts the string representation of a
  symbol into the datatype version.

  \end{description}
*}


subsection {* Qualified names *}

text {*
  A \emph{qualified name} essentially consists of a non-empty list of
  basic name components.  The packad notation uses a dot as separator,
  as in @{text "A.b"}, for example.  The very last component is called
  \emph{base} name, the remaining prefix \emph{qualifier} (which may
  be empty).

  A @{text "naming"} policy tells how to produce fully qualified names
  from a given specification.  The @{text "full"} operation applies
  performs naming of a name; the policy is usually taken from the
  context.  For example, a common policy is to attach an implicit
  prefix.

  A @{text "name space"} manages declarations of fully qualified
  names.  There are separate operations to @{text "declare"}, @{text
  "intern"}, and @{text "extern"} names.

  FIXME
*}

text %mlref FIXME


section {* Structured output *}

subsection {* Pretty printing *}

text FIXME

subsection {* Output channels *}

text FIXME

subsection {* Print modes \label{sec:print-mode} *}

text FIXME


end
