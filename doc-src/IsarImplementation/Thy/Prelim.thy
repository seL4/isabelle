theory Prelim
imports Base
begin

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

text {* A \emph{theory} is a data container with explicit name and
  unique identifier.  Theories are related by a (nominal) sub-theory
  relation, which corresponds to the dependency graph of the original
  construction; each theory is derived from a certain sub-graph of
  ancestor theories.  To this end, the system maintains a set of
  symbolic ``identification stamps'' within each theory.

  In order to avoid the full-scale overhead of explicit sub-theory
  identification of arbitrary intermediate stages, a theory is
  switched into @{text "draft"} mode under certain circumstances.  A
  draft theory acts like a linear type, where updates invalidate
  earlier versions.  An invalidated draft is called \emph{stale}.

  The @{text "checkpoint"} operation produces a safe stepping stone
  that will survive the next update without becoming stale: both the
  old and the new theory remain valid and are related by the
  sub-theory relation.  Checkpointing essentially recovers purely
  functional theory values, at the expense of some extra internal
  bookkeeping.

  The @{text "copy"} operation produces an auxiliary version that has
  the same data content, but is unrelated to the original: updates of
  the copy do not affect the original, neither does the sub-theory
  relation hold.

  The @{text "merge"} operation produces the least upper bound of two
  theories, which actually degenerates into absorption of one theory
  into the other (according to the nominal sub-theory relation).

  The @{text "begin"} operation starts a new theory by importing
  several parent theories and entering a special mode of nameless
  incremental updates, until the final @{text "end"} operation is
  performed.

  \medskip The example in \figref{fig:ex-theory} below shows a theory
  graph derived from @{text "Pure"}, with theory @{text "Length"}
  importing @{text "Nat"} and @{text "List"}.  The body of @{text
  "Length"} consists of a sequence of updates, working mostly on
  drafts internally, while transaction boundaries of Isar top-level
  commands (\secref{sec:isar-toplevel}) are guaranteed to be safe
  checkpoints.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{rcccl}
        &            & @{text "Pure"} \\
        &            & @{text "\<down>"} \\
        &            & @{text "FOL"} \\
        & $\swarrow$ &              & $\searrow$ & \\
  @{text "Nat"} &    &              &            & @{text "List"} \\
        & $\searrow$ &              & $\swarrow$ \\
        &            & @{text "Length"} \\
        &            & \multicolumn{3}{l}{~~@{keyword "imports"}} \\
        &            & \multicolumn{3}{l}{~~@{keyword "begin"}} \\
        &            & $\vdots$~~ \\
        &            & @{text "\<bullet>"}~~ \\
        &            & $\vdots$~~ \\
        &            & @{text "\<bullet>"}~~ \\
        &            & $\vdots$~~ \\
        &            & \multicolumn{3}{l}{~~@{command "end"}} \\
  \end{tabular}
  \caption{A theory definition depending on ancestors}\label{fig:ex-theory}
  \end{center}
  \end{figure}

  \medskip There is a separate notion of \emph{theory reference} for
  maintaining a live link to an evolving theory context: updates on
  drafts are propagated automatically.  Dynamic updating stops after
  an explicit @{text "end"} only.

  Derived entities may store a theory reference in order to indicate
  the context they belong to.  This implicitly assumes monotonic
  reasoning, because the referenced context may become larger without
  further notice.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type theory} \\
  @{index_ML Theory.subthy: "theory * theory -> bool"} \\
  @{index_ML Theory.checkpoint: "theory -> theory"} \\
  @{index_ML Theory.copy: "theory -> theory"} \\
  @{index_ML Theory.merge: "theory * theory -> theory"} \\
  @{index_ML Theory.begin_theory: "string -> theory list -> theory"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type theory_ref} \\
  @{index_ML Theory.deref: "theory_ref -> theory"} \\
  @{index_ML Theory.check_thy: "theory -> theory_ref"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type theory} represents theory contexts.  This is
  essentially a linear type, with explicit runtime checking!  Most
  internal theory operations destroy the original version, which then
  becomes ``stale''.

  \item @{ML "Theory.subthy"}~@{text "(thy\<^sub>1, thy\<^sub>2)"} compares theories
  according to the intrinsic graph structure of the construction.
  This sub-theory relation is a nominal approximation of inclusion
  (@{text "\<subseteq>"}) of the corresponding content (according to the
  semantics of the ML modules that implement the data).

  \item @{ML "Theory.checkpoint"}~@{text "thy"} produces a safe
  stepping stone in the linear development of @{text "thy"}.  This
  changes the old theory, but the next update will result in two
  related, valid theories.

  \item @{ML "Theory.copy"}~@{text "thy"} produces a variant of @{text
  "thy"} with the same data.  The copy is not related to the original,
  but the original is unchanged.

  \item @{ML "Theory.merge"}~@{text "(thy\<^sub>1, thy\<^sub>2)"} absorbs one theory
  into the other, without changing @{text "thy\<^sub>1"} or @{text "thy\<^sub>2"}.
  This version of ad-hoc theory merge fails for unrelated theories!

  \item @{ML "Theory.begin_theory"}~@{text "name parents"} constructs
  a new theory based on the given parents.  This {\ML} function is
  normally not invoked directly.

  \item @{ML_type theory_ref} represents a sliding reference to an
  always valid theory; updates on the original are propagated
  automatically.

  \item @{ML "Theory.deref"}~@{text "thy_ref"} turns a @{ML_type
  "theory_ref"} into an @{ML_type "theory"} value.  As the referenced
  theory evolves monotonically over time, later invocations of @{ML
  "Theory.deref"} may refer to a larger context.

  \item @{ML "Theory.check_thy"}~@{text "thy"} produces a @{ML_type
  "theory_ref"} from a valid @{ML_type "theory"} value.

  \end{description}
*}

text %mlex {*
  The following artificial example demonstrates theory
  data: we maintain a set of terms that are supposed to be wellformed
  wrt.\ the enclosing theory.  The public interface is as follows:
*}

ML {*
signature WELLFORMED_TERMS =
sig
  val get: theory -> term list
  val add: term -> theory -> theory
end;
*}

text {* \noindent The implementation uses private theory data
  internally, and only exposes an operation that involves explicit
  argument checking wrt.\ the given theory. *}

ML {*
structure Wellformed_Terms: WELLFORMED_TERMS =
struct

structure Terms = Theory_Data
(
  type T = term OrdList.T;
  val empty = [];
  val extend = I;
  fun merge (ts1, ts2) =
    OrdList.union TermOrd.fast_term_ord ts1 ts2;
)

val get = Terms.get;

fun add raw_t thy =
  let val t = Sign.cert_term thy raw_t
  in Terms.map (OrdList.insert TermOrd.fast_term_ord t) thy end;

end;
*}

text {* We use @{ML_type "term OrdList.T"} for reasonably efficient
  representation of a set of terms: all operations are linear in the
  number of stored elements.  Here we assume that our users do not
  care about the declaration order, since that data structure forces
  its own arrangement of elements.

  Observe how the @{verbatim merge} operation joins the data slots of
  the two constituents: @{ML OrdList.union} prevents duplication of
  common data from different branches, thus avoiding the danger of
  exponential blowup.  (Plain list append etc.\ must never be used for
  theory data merges.)

  \medskip Our intended invariant is achieved as follows:
  \begin{enumerate}

  \item @{ML Wellformed_Terms.add} only admits terms that have passed
  the @{ML Sign.cert_term} check of the given theory at that point.

  \item Wellformedness in the sense of @{ML Sign.cert_term} is
  monotonic wrt.\ the sub-theory relation.  So our data can move
  upwards in the hierarchy (via extension or merges), and maintain
  wellformedness without further checks.

  \end{enumerate}

  Note that all basic operations of the inference kernel (which
  includes @{ML Sign.cert_term}) observe this monotonicity principle,
  but other user-space tools don't.  For example, fully-featured
  type-inference via @{ML Syntax.check_term} (cf.\
  \secref{sec:term-check}) is not necessarily monotonic wrt.\ the
  background theory, since constraints of term constants can be
  strengthened by later declarations, for example.

  In most cases, user-space context data does not have to take such
  invariants too seriously.  The situation is different in the
  implementation of the inference kernel itself, which uses the very
  same data mechanisms for types, constants, axioms etc.
*}


subsection {* Proof context \label{sec:context-proof} *}

text {* A proof context is a container for pure data with a
  back-reference to the theory it belongs to.  The @{text "init"}
  operation creates a proof context from a given theory.
  Modifications to draft theories are propagated to the proof context
  as usual, but there is also an explicit @{text "transfer"} operation
  to force resynchronization with more substantial updates to the
  underlying theory.

  Entities derived in a proof context need to record logical
  requirements explicitly, since there is no separate context
  identification or symbolic inclusion as for theories.  For example,
  hypotheses used in primitive derivations (cf.\ \secref{sec:thms})
  are recorded separately within the sequent @{text "\<Gamma> \<turnstile> \<phi>"}, just to
  make double sure.  Results could still leak into an alien proof
  context due to programming errors, but Isabelle/Isar includes some
  extra validity checks in critical positions, notably at the end of a
  sub-proof.

  Proof contexts may be manipulated arbitrarily, although the common
  discipline is to follow block structure as a mental model: a given
  context is extended consecutively, and results are exported back
  into the original context.  Note that an Isar proof state models
  block-structured reasoning explicitly, using a stack of proof
  contexts internally.  For various technical reasons, the background
  theory of an Isar proof state must not be changed while the proof is
  still under construction!
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
  have to be constructed by an ad-hoc @{text "init"} operation, which
  incurs a small runtime overhead.
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


subsection {* Context data \label{sec:context-data} *}

text {* The main purpose of theory and proof contexts is to manage
  arbitrary (pure) data.  New data types can be declared incrementally
  at compile time.  There are separate declaration mechanisms for any
  of the three kinds of contexts: theory, proof, generic.

  \paragraph{Theory data} declarations need to implement the following
  SML signature:

  \medskip
  \begin{tabular}{ll}
  @{text "\<type> T"} & representing type \\
  @{text "\<val> empty: T"} & empty default value \\
  @{text "\<val> extend: T \<rightarrow> T"} & re-initialize on import \\
  @{text "\<val> merge: T \<times> T \<rightarrow> T"} & join on import \\
  \end{tabular}
  \medskip

  \noindent The @{text "empty"} value acts as initial default for
  \emph{any} theory that does not declare actual data content; @{text
  "extend"} is acts like a unitary version of @{text "merge"}.

  Implementing @{text "merge"} can be tricky.  The general idea is
  that @{text "merge (data\<^sub>1, data\<^sub>2)"} inserts those parts of @{text
  "data\<^sub>2"} into @{text "data\<^sub>1"} that are not yet present, while
  keeping the general order of things.  The @{ML Library.merge}
  function on plain lists may serve as canonical template.

  Particularly note that shared parts of the data must not be
  duplicated by naive concatenation, or a theory graph that is like a
  chain of diamonds would cause an exponential blowup!

  \paragraph{Proof context data} declarations need to implement the
  following SML signature:

  \medskip
  \begin{tabular}{ll}
  @{text "\<type> T"} & representing type \\
  @{text "\<val> init: theory \<rightarrow> T"} & produce initial value \\
  \end{tabular}
  \medskip

  \noindent The @{text "init"} operation is supposed to produce a pure
  value from the given background theory and should be somehow
  ``immediate''.  Whenever a proof context is initialized, which
  happens frequently, the the system invokes the @{text "init"}
  operation of \emph{all} theory data slots ever declared.

  \paragraph{Generic data} provides a hybrid interface for both theory
  and proof data.  The @{text "init"} operation for proof contexts is
  predefined to select the current data value from the background
  theory.

  \bigskip Any of these data declaration over type @{text "T"} result
  in an ML structure with the following signature:

  \medskip
  \begin{tabular}{ll}
  @{text "get: context \<rightarrow> T"} \\
  @{text "put: T \<rightarrow> context \<rightarrow> context"} \\
  @{text "map: (T \<rightarrow> T) \<rightarrow> context \<rightarrow> context"} \\
  \end{tabular}
  \medskip

  \noindent These other operations provide exclusive access for the
  particular kind of context (theory, proof, or generic context).
  This interface fully observes the ML discipline for types and
  scopes: there is no other way to access the corresponding data slot
  of a context.  By keeping these operations private, an Isabelle/ML
  module may maintain abstract values authentically.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_functor Theory_Data} \\
  @{index_ML_functor Proof_Data} \\
  @{index_ML_functor Generic_Data} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_functor Theory_Data}@{text "(spec)"} declares data for
  type @{ML_type theory} according to the specification provided as
  argument structure.  The resulting structure provides data init and
  access operations as described above.

  \item @{ML_functor Proof_Data}@{text "(spec)"} is analogous to
  @{ML_functor Theory_Data} for type @{ML_type Proof.context}.

  \item @{ML_functor Generic_Data}@{text "(spec)"} is analogous to
  @{ML_functor Theory_Data} for type @{ML_type Context.generic}.

  \end{description}
*}


section {* Names \label{sec:names} *}

text {* In principle, a name is just a string, but there are various
  conventions for representing additional structure.  For example,
  ``@{text "Foo.bar.baz"}'' is considered as a qualified name
  consisting of three basic name components.  The individual
  constituents of a name may have further substructure, e.g.\ the
  string ``\verb,\,\verb,<alpha>,'' encodes as a single symbol.
*}


subsection {* Strings of symbols *}

text {* A \emph{symbol} constitutes the smallest textual unit in
  Isabelle --- raw ML characters are normally not encountered at all!
  Isabelle strings consist of a sequence of symbols, represented as a
  packed string or an exploded list of strings.  Each symbol is in
  itself a small string, which has either one of the following forms:

  \begin{enumerate}

  \item a single ASCII character ``@{text "c"}'' or raw byte in the
  range of 128\dots 255, for example ``\verb,a,'',

  \item a regular symbol ``\verb,\,\verb,<,@{text "ident"}\verb,>,'',
  for example ``\verb,\,\verb,<alpha>,'',

  \item a control symbol ``\verb,\,\verb,<^,@{text "ident"}\verb,>,'',
  for example ``\verb,\,\verb,<^bold>,'',

  \item a raw symbol ``\verb,\,\verb,<^raw:,@{text text}\verb,>,''
  where @{text text} consists of printable characters excluding
  ``\verb,.,'' and ``\verb,>,'', for example
  ``\verb,\,\verb,<^raw:$\sum_{i = 1}^n$>,'',

  \item a numbered raw control symbol ``\verb,\,\verb,<^raw,@{text
  n}\verb,>, where @{text n} consists of digits, for example
  ``\verb,\,\verb,<^raw42>,''.

  \end{enumerate}

  \noindent The @{text "ident"} syntax for symbol names is @{text
  "letter (letter | digit)\<^sup>*"}, where @{text "letter =
  A..Za..z"} and @{text "digit = 0..9"}.  There are infinitely many
  regular symbols and control symbols, but a fixed collection of
  standard symbols is treated specifically.  For example,
  ``\verb,\,\verb,<alpha>,'' is classified as a letter, which means it
  may occur within regular Isabelle identifiers.

  Since the character set underlying Isabelle symbols is 7-bit ASCII
  and 8-bit characters are passed through transparently, Isabelle can
  also process Unicode/UCS data in UTF-8 encoding.\footnote{When
  counting precise source positions internally, bytes in the range of
  128\dots 191 are ignored.  In UTF-8 encoding, this interval covers
  the additional trailer bytes, so Isabelle happens to count Unicode
  characters here, not bytes in memory.  In ISO-Latin encoding, the
  ignored range merely includes some extra punctuation characters that
  even have replacements within the standard collection of Isabelle
  symbols; the accented letters range is counted properly.} Unicode
  provides its own collection of mathematical symbols, but within the
  core Isabelle/ML world there is no link to the standard collection
  of Isabelle regular symbols.

  \medskip Output of Isabelle symbols depends on the print mode
  (\secref{print-mode}).  For example, the standard {\LaTeX} setup of
  the Isabelle document preparation system would present
  ``\verb,\,\verb,<alpha>,'' as @{text "\<alpha>"}, and
  ``\verb,\,\verb,<^bold>,\verb,\,\verb,<alpha>,'' as @{text
  "\<^bold>\<alpha>"}.  On-screen rendering usually works by mapping a finite
  subset of Isabelle symbols to suitable Unicode characters.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type "Symbol.symbol": string} \\
  @{index_ML Symbol.explode: "string -> Symbol.symbol list"} \\
  @{index_ML Symbol.is_letter: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_digit: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_quasi: "Symbol.symbol -> bool"} \\
  @{index_ML Symbol.is_blank: "Symbol.symbol -> bool"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type "Symbol.sym"} \\
  @{index_ML Symbol.decode: "Symbol.symbol -> Symbol.sym"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type "Symbol.symbol"} represents individual Isabelle
  symbols.

  \item @{ML "Symbol.explode"}~@{text "str"} produces a symbol list
  from the packed form.  This function supercedes @{ML
  "String.explode"} for virtually all purposes of manipulating text in
  Isabelle!\footnote{The runtime overhead for exploded strings is
  mainly that of the list structure: individual symbols that happen to
  be a singleton string --- which is the most common case --- do not
  require extra memory in Poly/ML.}

  \item @{ML "Symbol.is_letter"}, @{ML "Symbol.is_digit"}, @{ML
  "Symbol.is_quasi"}, @{ML "Symbol.is_blank"} classify standard
  symbols according to fixed syntactic conventions of Isabelle, cf.\
  \cite{isabelle-isar-ref}.

  \item @{ML_type "Symbol.sym"} is a concrete datatype that represents
  the different kinds of symbols explicitly, with constructors @{ML
  "Symbol.Char"}, @{ML "Symbol.Sym"}, @{ML "Symbol.Ctrl"}, @{ML
  "Symbol.Raw"}.

  \item @{ML "Symbol.decode"} converts the string representation of a
  symbol into the datatype version.

  \end{description}

  \paragraph{Historical note.} In the original SML90 standard the
  primitive ML type @{ML_type char} did not exists, and the basic @{ML
  "explode: string -> string list"} operation would produce a list of
  singleton strings as in Isabelle/ML today.  When SML97 came out,
  Isabelle ignored its slightly anachronistic 8-bit characters, but
  the idea of exploding a string into a list of small strings was
  extended to ``symbols'' as explained above.  Thus Isabelle sources
  can refer to an infinite store of user-defined symbols, without
  having to worry about the multitude of Unicode encodings.
*}


subsection {* Basic names \label{sec:basic-names} *}

text {*
  A \emph{basic name} essentially consists of a single Isabelle
  identifier.  There are conventions to mark separate classes of basic
  names, by attaching a suffix of underscores: one underscore means
  \emph{internal name}, two underscores means \emph{Skolem name},
  three underscores means \emph{internal Skolem name}.

  For example, the basic name @{text "foo"} has the internal version
  @{text "foo_"}, with Skolem versions @{text "foo__"} and @{text
  "foo___"}, respectively.

  These special versions provide copies of the basic name space, apart
  from anything that normally appears in the user text.  For example,
  system generated variables in Isar proof contexts are usually marked
  as internal, which prevents mysterious names like @{text "xaa"} to
  appear in human-readable text.

  \medskip Manipulating binding scopes often requires on-the-fly
  renamings.  A \emph{name context} contains a collection of already
  used names.  The @{text "declare"} operation adds names to the
  context.

  The @{text "invents"} operation derives a number of fresh names from
  a given starting point.  For example, the first three names derived
  from @{text "a"} are @{text "a"}, @{text "b"}, @{text "c"}.

  The @{text "variants"} operation produces fresh names by
  incrementing tentative names as base-26 numbers (with digits @{text
  "a..z"}) until all clashes are resolved.  For example, name @{text
  "foo"} results in variants @{text "fooa"}, @{text "foob"}, @{text
  "fooc"}, \dots, @{text "fooaa"}, @{text "fooab"} etc.; each renaming
  step picks the next unused variant from this sequence.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Name.internal: "string -> string"} \\
  @{index_ML Name.skolem: "string -> string"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name.context} \\
  @{index_ML Name.context: Name.context} \\
  @{index_ML Name.declare: "string -> Name.context -> Name.context"} \\
  @{index_ML Name.invents: "Name.context -> string -> int -> string list"} \\
  @{index_ML Name.variants: "string list -> Name.context -> string list * Name.context"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML Variable.names_of: "Proof.context -> Name.context"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Name.internal}~@{text "name"} produces an internal name
  by adding one underscore.

  \item @{ML Name.skolem}~@{text "name"} produces a Skolem name by
  adding two underscores.

  \item @{ML_type Name.context} represents the context of already used
  names; the initial value is @{ML "Name.context"}.

  \item @{ML Name.declare}~@{text "name"} enters a used name into the
  context.

  \item @{ML Name.invents}~@{text "context name n"} produces @{text
  "n"} fresh names derived from @{text "name"}.

  \item @{ML Name.variants}~@{text "names context"} produces fresh
  variants of @{text "names"}; the result is entered into the context.

  \item @{ML Variable.names_of}~@{text "ctxt"} retrieves the context
  of declared type and term variable names.  Projecting a proof
  context down to a primitive name context is occasionally useful when
  invoking lower-level operations.  Regular management of ``fresh
  variables'' is done by suitable operations of structure @{ML_struct
  Variable}, which is also able to provide an official status of
  ``locally fixed variable'' within the logical environment (cf.\
  \secref{sec:variables}).

  \end{description}
*}


subsection {* Indexed names *}

text {*
  An \emph{indexed name} (or @{text "indexname"}) is a pair of a basic
  name and a natural number.  This representation allows efficient
  renaming by incrementing the second component only.  The canonical
  way to rename two collections of indexnames apart from each other is
  this: determine the maximum index @{text "maxidx"} of the first
  collection, then increment all indexes of the second collection by
  @{text "maxidx + 1"}; the maximum index of an empty collection is
  @{text "-1"}.

  Occasionally, basic names and indexed names are injected into the
  same pair type: the (improper) indexname @{text "(x, -1)"} is used
  to encode the basic name @{text "x"}.

  \medskip Isabelle syntax observes the following rules for
  representing an indexname @{text "(x, i)"} as a packed string:

  \begin{itemize}

  \item @{text "?x"} if @{text "x"} does not end with a digit and @{text "i = 0"},

  \item @{text "?xi"} if @{text "x"} does not end with a digit,

  \item @{text "?x.i"} otherwise.

  \end{itemize}

  Indexnames may acquire large index numbers over time.  Results are
  normalized towards @{text "0"} at certain checkpoints, notably at
  the end of a proof.  This works by producing variants of the
  corresponding basic name components.  For example, the collection
  @{text "?x1, ?x7, ?x42"} becomes @{text "?x, ?xa, ?xb"}.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type indexname} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type indexname} represents indexed names.  This is an
  abbreviation for @{ML_type "string * int"}.  The second component is
  usually non-negative, except for situations where @{text "(x, -1)"}
  is used to inject basic names into this type.  Other negative
  indexes should not be used.

  \end{description}
*}


subsection {* Qualified names and name spaces *}

text {*
  A \emph{qualified name} consists of a non-empty sequence of basic
  name components.  The packed representation uses a dot as separator,
  as in ``@{text "A.b.c"}''.  The last component is called \emph{base}
  name, the remaining prefix \emph{qualifier} (which may be empty).
  The idea of qualified names is to encode nested structures by
  recording the access paths as qualifiers.  For example, an item
  named ``@{text "A.b.c"}'' may be understood as a local entity @{text
  "c"}, within a local structure @{text "b"}, within a global
  structure @{text "A"}.  Typically, name space hierarchies consist of
  1--2 levels of qualification, but this need not be always so.

  The empty name is commonly used as an indication of unnamed
  entities, whenever this makes any sense.  The basic operations on
  qualified names are smart enough to pass through such improper names
  unchanged.

  \medskip A @{text "naming"} policy tells how to turn a name
  specification into a fully qualified internal name (by the @{text
  "full"} operation), and how fully qualified names may be accessed
  externally.  For example, the default naming policy is to prefix an
  implicit path: @{text "full x"} produces @{text "path.x"}, and the
  standard accesses for @{text "path.x"} include both @{text "x"} and
  @{text "path.x"}.  Normally, the naming is implicit in the theory or
  proof context; there are separate versions of the corresponding.

  \medskip A @{text "name space"} manages a collection of fully
  internalized names, together with a mapping between external names
  and internal names (in both directions).  The corresponding @{text
  "intern"} and @{text "extern"} operations are mostly used for
  parsing and printing only!  The @{text "declare"} operation augments
  a name space according to the accesses determined by the naming
  policy.

  \medskip As a general principle, there is a separate name space for
  each kind of formal entity, e.g.\ logical constant, type
  constructor, type class, theorem.  It is usually clear from the
  occurrence in concrete syntax (or from the scope) which kind of
  entity a name refers to.  For example, the very same name @{text
  "c"} may be used uniformly for a constant, type constructor, and
  type class.

  There are common schemes to name theorems systematically, according
  to the name of the main logical entity involved, e.g.\ @{text
  "c.intro"} for a canonical theorem related to constant @{text "c"}.
  This technique of mapping names from one space into another requires
  some care in order to avoid conflicts.  In particular, theorem names
  derived from a type constructor or type class are better suffixed in
  addition to the usual qualification, e.g.\ @{text "c_type.intro"}
  and @{text "c_class.intro"} for theorems related to type @{text "c"}
  and class @{text "c"}, respectively.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Long_Name.base_name: "string -> string"} \\
  @{index_ML Long_Name.qualifier: "string -> string"} \\
  @{index_ML Long_Name.append: "string -> string -> string"} \\
  @{index_ML Long_Name.implode: "string list -> string"} \\
  @{index_ML Long_Name.explode: "string -> string list"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name_Space.naming} \\
  @{index_ML Name_Space.default_naming: Name_Space.naming} \\
  @{index_ML Name_Space.add_path: "string -> Name_Space.naming -> Name_Space.naming"} \\
  @{index_ML Name_Space.full_name: "Name_Space.naming -> binding -> string"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name_Space.T} \\
  @{index_ML Name_Space.empty: "string -> Name_Space.T"} \\
  @{index_ML Name_Space.merge: "Name_Space.T * Name_Space.T -> Name_Space.T"} \\
  @{index_ML Name_Space.declare: "bool -> Name_Space.naming -> binding -> Name_Space.T ->
  string * Name_Space.T"} \\
  @{index_ML Name_Space.intern: "Name_Space.T -> string -> string"} \\
  @{index_ML Name_Space.extern: "Name_Space.T -> string -> string"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Long_Name.base_name}~@{text "name"} returns the base name of a
  qualified name.

  \item @{ML Long_Name.qualifier}~@{text "name"} returns the qualifier
  of a qualified name.

  \item @{ML Long_Name.append}~@{text "name\<^isub>1 name\<^isub>2"}
  appends two qualified names.

  \item @{ML Long_Name.implode}~@{text "names"} and @{ML
  Long_Name.explode}~@{text "name"} convert between the packed string
  representation and the explicit list form of qualified names.

  \item @{ML_type Name_Space.naming} represents the abstract concept of
  a naming policy.

  \item @{ML Name_Space.default_naming} is the default naming policy.
  In a theory context, this is usually augmented by a path prefix
  consisting of the theory name.

  \item @{ML Name_Space.add_path}~@{text "path naming"} augments the
  naming policy by extending its path component.

  \item @{ML Name_Space.full_name}~@{text "naming binding"} turns a
  name binding (usually a basic name) into the fully qualified
  internal name, according to the given naming policy.

  \item @{ML_type Name_Space.T} represents name spaces.

  \item @{ML Name_Space.empty}~@{text "kind"} and @{ML Name_Space.merge}~@{text
  "(space\<^isub>1, space\<^isub>2)"} are the canonical operations for
  maintaining name spaces according to theory data management
  (\secref{sec:context-data}); @{text "kind"} is a formal comment
  to characterize the purpose of a name space.

  \item @{ML Name_Space.declare}~@{text "strict naming bindings
  space"} enters a name binding as fully qualified internal name into
  the name space, with external accesses determined by the naming
  policy.

  \item @{ML Name_Space.intern}~@{text "space name"} internalizes a
  (partially qualified) external name.

  This operation is mostly for parsing!  Note that fully qualified
  names stemming from declarations are produced via @{ML
  "Name_Space.full_name"} and @{ML "Name_Space.declare"}
  (or their derivatives for @{ML_type theory} and
  @{ML_type Proof.context}).

  \item @{ML Name_Space.extern}~@{text "space name"} externalizes a
  (fully qualified) internal name.

  This operation is mostly for printing!  User code should not rely on
  the precise result too much.

  \end{description}
*}

end
