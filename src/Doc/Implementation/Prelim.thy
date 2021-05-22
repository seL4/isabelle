(*:maxLineLen=78:*)

theory Prelim
imports Base
begin

chapter \<open>Preliminaries\<close>

section \<open>Contexts \label{sec:context}\<close>

text \<open>
  A logical context represents the background that is required for formulating
  statements and composing proofs. It acts as a medium to produce formal
  content, depending on earlier material (declarations, results etc.).

  For example, derivations within the Isabelle/Pure logic can be described as
  a judgment \<open>\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>\<close>, which means that a proposition \<open>\<phi>\<close> is derivable from
  hypotheses \<open>\<Gamma>\<close> within the theory \<open>\<Theta>\<close>. There are logical reasons for keeping
  \<open>\<Theta>\<close> and \<open>\<Gamma>\<close> separate: theories can be liberal about supporting type
  constructors and schematic polymorphism of constants and axioms, while the
  inner calculus of \<open>\<Gamma> \<turnstile> \<phi>\<close> is strictly limited to Simple Type Theory (with
  fixed type variables in the assumptions).

  \<^medskip>
  Contexts and derivations are linked by the following key principles:

  \<^item> Transfer: monotonicity of derivations admits results to be transferred
  into a \<^emph>\<open>larger\<close> context, i.e.\ \<open>\<Gamma> \<turnstile>\<^sub>\<Theta> \<phi>\<close> implies \<open>\<Gamma>' \<turnstile>\<^sub>\<Theta>\<^sub>' \<phi>\<close> for contexts
  \<open>\<Theta>' \<supseteq> \<Theta>\<close> and \<open>\<Gamma>' \<supseteq> \<Gamma>\<close>.

  \<^item> Export: discharge of hypotheses admits results to be exported into a
  \<^emph>\<open>smaller\<close> context, i.e.\ \<open>\<Gamma>' \<turnstile>\<^sub>\<Theta> \<phi>\<close> implies \<open>\<Gamma> \<turnstile>\<^sub>\<Theta> \<Delta> \<Longrightarrow> \<phi>\<close> where \<open>\<Gamma>' \<supseteq> \<Gamma>\<close>
  and \<open>\<Delta> = \<Gamma>' - \<Gamma>\<close>. Note that \<open>\<Theta>\<close> remains unchanged here, only the \<open>\<Gamma>\<close> part is
  affected.


  \<^medskip>
  By modeling the main characteristics of the primitive \<open>\<Theta>\<close> and \<open>\<Gamma>\<close> above, and
  abstracting over any particular logical content, we arrive at the
  fundamental notions of \<^emph>\<open>theory context\<close> and \<^emph>\<open>proof context\<close> in
  Isabelle/Isar. These implement a certain policy to manage arbitrary
  \<^emph>\<open>context data\<close>. There is a strongly-typed mechanism to declare new kinds of
  data at compile time.

  The internal bootstrap process of Isabelle/Pure eventually reaches a stage
  where certain data slots provide the logical content of \<open>\<Theta>\<close> and \<open>\<Gamma>\<close> sketched
  above, but this does not stop there! Various additional data slots support
  all kinds of mechanisms that are not necessarily part of the core logic.

  For example, there would be data for canonical introduction and elimination
  rules for arbitrary operators (depending on the object-logic and
  application), which enables users to perform standard proof steps implicitly
  (cf.\ the \<open>rule\<close> method @{cite "isabelle-isar-ref"}).

  \<^medskip>
  Thus Isabelle/Isar is able to bring forth more and more concepts
  successively. In particular, an object-logic like Isabelle/HOL continues the
  Isabelle/Pure setup by adding specific components for automated reasoning
  (classical reasoner, tableau prover, structured induction etc.) and derived
  specification mechanisms (inductive predicates, recursive functions etc.).
  All of this is ultimately based on the generic data management by theory and
  proof contexts introduced here.
\<close>


subsection \<open>Theory context \label{sec:context-theory}\<close>

text \<open>
  A \<^emph>\<open>theory\<close> is a data container with explicit name and unique identifier.
  Theories are related by a (nominal) sub-theory relation, which corresponds
  to the dependency graph of the original construction; each theory is derived
  from a certain sub-graph of ancestor theories. To this end, the system
  maintains a set of symbolic ``identification stamps'' within each theory.

  The \<open>begin\<close> operation starts a new theory by importing several parent
  theories (with merged contents) and entering a special mode of nameless
  incremental updates, until the final \<open>end\<close> operation is performed.

  \<^medskip>
  The example in \figref{fig:ex-theory} below shows a theory graph derived
  from \<open>Pure\<close>, with theory \<open>Length\<close> importing \<open>Nat\<close> and \<open>List\<close>. The body of
  \<open>Length\<close> consists of a sequence of updates, resulting in locally a linear
  sub-theory relation for each intermediate step.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{rcccl}
        &            & \<open>Pure\<close> \\
        &            & \<open>\<down>\<close> \\
        &            & \<open>FOL\<close> \\
        & $\swarrow$ &              & $\searrow$ & \\
  \<open>Nat\<close> &    &              &            & \<open>List\<close> \\
        & $\searrow$ &              & $\swarrow$ \\
        &            & \<open>Length\<close> \\
        &            & \multicolumn{3}{l}{~~@{keyword "begin"}} \\
        &            & $\vdots$~~ \\
        &            & \multicolumn{3}{l}{~~@{command "end"}} \\
  \end{tabular}
  \caption{A theory definition depending on ancestors}\label{fig:ex-theory}
  \end{center}
  \end{figure}

  \<^medskip>
  Derived formal entities may retain a reference to the background theory in
  order to indicate the formal context from which they were produced. This
  provides an immutable certificate of the background theory.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type theory} \\
  @{index_ML Context.eq_thy: "theory * theory -> bool"} \\
  @{index_ML Context.subthy: "theory * theory -> bool"} \\
  @{index_ML Theory.begin_theory: "string * Position.T -> theory list -> theory"} \\
  @{index_ML Theory.parents_of: "theory -> theory list"} \\
  @{index_ML Theory.ancestors_of: "theory -> theory list"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>theory\<close> represents theory contexts.

  \<^descr> \<^ML>\<open>Context.eq_thy\<close>~\<open>(thy\<^sub>1, thy\<^sub>2)\<close> check strict identity of two
  theories.

  \<^descr> \<^ML>\<open>Context.subthy\<close>~\<open>(thy\<^sub>1, thy\<^sub>2)\<close> compares theories according to the
  intrinsic graph structure of the construction. This sub-theory relation is a
  nominal approximation of inclusion (\<open>\<subseteq>\<close>) of the corresponding content
  (according to the semantics of the ML modules that implement the data).

  \<^descr> \<^ML>\<open>Theory.begin_theory\<close>~\<open>name parents\<close> constructs a new theory based
  on the given parents. This ML function is normally not invoked directly.

  \<^descr> \<^ML>\<open>Theory.parents_of\<close>~\<open>thy\<close> returns the direct ancestors of \<open>thy\<close>.

  \<^descr> \<^ML>\<open>Theory.ancestors_of\<close>~\<open>thy\<close> returns all ancestors of \<open>thy\<close> (not
  including \<open>thy\<close> itself).
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "theory"} & : & \<open>ML_antiquotation\<close> \\
  @{ML_antiquotation_def "theory_context"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation theory} embedded?
  ;
  @@{ML_antiquotation theory_context} embedded
  \<close>

  \<^descr> \<open>@{theory}\<close> refers to the background theory of the current context --- as
  abstract value.

  \<^descr> \<open>@{theory A}\<close> refers to an explicitly named ancestor theory \<open>A\<close> of the
  background theory of the current context --- as abstract value.

  \<^descr> \<open>@{theory_context A}\<close> is similar to \<open>@{theory A}\<close>, but presents the result
  as initial \<^ML_type>\<open>Proof.context\<close> (see also \<^ML>\<open>Proof_Context.init_global\<close>).
\<close>


subsection \<open>Proof context \label{sec:context-proof}\<close>

text \<open>
  A proof context is a container for pure data that refers to the theory from
  which it is derived. The \<open>init\<close> operation creates a proof context from a
  given theory. There is an explicit \<open>transfer\<close> operation to force
  resynchronization with updates to the background theory -- this is rarely
  required in practice.

  Entities derived in a proof context need to record logical requirements
  explicitly, since there is no separate context identification or symbolic
  inclusion as for theories. For example, hypotheses used in primitive
  derivations (cf.\ \secref{sec:thms}) are recorded separately within the
  sequent \<open>\<Gamma> \<turnstile> \<phi>\<close>, just to make double sure. Results could still leak into an
  alien proof context due to programming errors, but Isabelle/Isar includes
  some extra validity checks in critical positions, notably at the end of a
  sub-proof.

  Proof contexts may be manipulated arbitrarily, although the common
  discipline is to follow block structure as a mental model: a given context
  is extended consecutively, and results are exported back into the original
  context. Note that an Isar proof state models block-structured reasoning
  explicitly, using a stack of proof contexts internally. For various
  technical reasons, the background theory of an Isar proof state must not be
  changed while the proof is still under construction!
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type Proof.context} \\
  @{index_ML Proof_Context.init_global: "theory -> Proof.context"} \\
  @{index_ML Proof_Context.theory_of: "Proof.context -> theory"} \\
  @{index_ML Proof_Context.transfer: "theory -> Proof.context -> Proof.context"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Proof.context\<close> represents proof contexts.

  \<^descr> \<^ML>\<open>Proof_Context.init_global\<close>~\<open>thy\<close> produces a proof context derived
  from \<open>thy\<close>, initializing all data.

  \<^descr> \<^ML>\<open>Proof_Context.theory_of\<close>~\<open>ctxt\<close> selects the background theory from
  \<open>ctxt\<close>.

  \<^descr> \<^ML>\<open>Proof_Context.transfer\<close>~\<open>thy ctxt\<close> promotes the background theory of
  \<open>ctxt\<close> to the super theory \<open>thy\<close>.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "context"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^descr> \<open>@{context}\<close> refers to \<^emph>\<open>the\<close> context at compile-time --- as abstract
  value. Independently of (local) theory or proof mode, this always produces a
  meaningful result.

  This is probably the most common antiquotation in interactive
  experimentation with ML inside Isar.
\<close>


subsection \<open>Generic contexts \label{sec:generic-context}\<close>

text \<open>
  A generic context is the disjoint sum of either a theory or proof context.
  Occasionally, this enables uniform treatment of generic context data,
  typically extra-logical information. Operations on generic contexts include
  the usual injections, partial selections, and combinators for lifting
  operations on either component of the disjoint sum.

  Moreover, there are total operations \<open>theory_of\<close> and \<open>proof_of\<close> to convert a
  generic context into either kind: a theory can always be selected from the
  sum, while a proof context might have to be constructed by an ad-hoc \<open>init\<close>
  operation, which incurs a small runtime overhead.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type Context.generic} \\
  @{index_ML Context.theory_of: "Context.generic -> theory"} \\
  @{index_ML Context.proof_of: "Context.generic -> Proof.context"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Context.generic\<close> is the direct sum of \<^ML_type>\<open>theory\<close>
  and \<^ML_type>\<open>Proof.context\<close>, with the datatype constructors \<^ML>\<open>Context.Theory\<close> and \<^ML>\<open>Context.Proof\<close>.

  \<^descr> \<^ML>\<open>Context.theory_of\<close>~\<open>context\<close> always produces a theory from the
  generic \<open>context\<close>, using \<^ML>\<open>Proof_Context.theory_of\<close> as required.

  \<^descr> \<^ML>\<open>Context.proof_of\<close>~\<open>context\<close> always produces a proof context from the
  generic \<open>context\<close>, using \<^ML>\<open>Proof_Context.init_global\<close> as required (note
  that this re-initializes the context data with each invocation).
\<close>


subsection \<open>Context data \label{sec:context-data}\<close>

text \<open>
  The main purpose of theory and proof contexts is to manage arbitrary (pure)
  data. New data types can be declared incrementally at compile time. There
  are separate declaration mechanisms for any of the three kinds of contexts:
  theory, proof, generic.
\<close>

paragraph \<open>Theory data\<close>
text \<open>declarations need to implement the following ML signature:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>\<type> T\<close> & representing type \\
  \<open>\<val> empty: T\<close> & empty default value \\
  \<open>\<val> extend: T \<rightarrow> T\<close> & obsolete (identity function) \\
  \<open>\<val> merge: T \<times> T \<rightarrow> T\<close> & merge data \\
  \end{tabular}
  \<^medskip>

  The \<open>empty\<close> value acts as initial default for \<^emph>\<open>any\<close> theory that does not
  declare actual data content; \<open>extend\<close> is obsolete: it needs to be the
  identity function.

  The \<open>merge\<close> operation needs to join the data from two theories in a
  conservative manner. The standard scheme for \<open>merge (data\<^sub>1, data\<^sub>2)\<close>
  inserts those parts of \<open>data\<^sub>2\<close> into \<open>data\<^sub>1\<close> that are not yet present,
  while keeping the general order of things. The \<^ML>\<open>Library.merge\<close>
  function on plain lists may serve as canonical template. Particularly note
  that shared parts of the data must not be duplicated by naive concatenation,
  or a theory graph that resembles a chain of diamonds would cause an
  exponential blowup!

  Sometimes, the data consists of a single item that cannot be ``merged'' in a
  sensible manner. Then the standard scheme degenerates to the projection to
  \<open>data\<^sub>1\<close>, ignoring \<open>data\<^sub>2\<close> outright.
\<close>

paragraph \<open>Proof context data\<close>
text \<open>declarations need to implement the following ML signature:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>\<type> T\<close> & representing type \\
  \<open>\<val> init: theory \<rightarrow> T\<close> & produce initial value \\
  \end{tabular}
  \<^medskip>

  The \<open>init\<close> operation is supposed to produce a pure value from the given
  background theory and should be somehow ``immediate''. Whenever a proof
  context is initialized, which happens frequently, the the system invokes the
  \<open>init\<close> operation of \<^emph>\<open>all\<close> theory data slots ever declared. This also means
  that one needs to be economic about the total number of proof data
  declarations in the system, i.e.\ each ML module should declare at most one,
  sometimes two data slots for its internal use. Repeated data declarations to
  simulate a record type should be avoided!
\<close>

paragraph \<open>Generic data\<close>
text \<open>
  provides a hybrid interface for both theory and proof data. The \<open>init\<close>
  operation for proof contexts is predefined to select the current data value
  from the background theory.

  \<^bigskip>
  Any of the above data declarations over type \<open>T\<close> result in an ML structure
  with the following signature:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>get: context \<rightarrow> T\<close> \\
  \<open>put: T \<rightarrow> context \<rightarrow> context\<close> \\
  \<open>map: (T \<rightarrow> T) \<rightarrow> context \<rightarrow> context\<close> \\
  \end{tabular}
  \<^medskip>

  These other operations provide exclusive access for the particular kind of
  context (theory, proof, or generic context). This interface observes the ML
  discipline for types and scopes: there is no other way to access the
  corresponding data slot of a context. By keeping these operations private,
  an Isabelle/ML module may maintain abstract values authentically.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_functor Theory_Data} \\
  @{index_ML_functor Proof_Data} \\
  @{index_ML_functor Generic_Data} \\
  \end{mldecls}

  \<^descr> \<^ML_functor>\<open>Theory_Data\<close>\<open>(spec)\<close> declares data for type \<^ML_type>\<open>theory\<close>
  according to the specification provided as argument structure. The resulting
  structure provides data init and access operations as described above.

  \<^descr> \<^ML_functor>\<open>Proof_Data\<close>\<open>(spec)\<close> is analogous to \<^ML_functor>\<open>Theory_Data\<close>
  for type \<^ML_type>\<open>Proof.context\<close>.

  \<^descr> \<^ML_functor>\<open>Generic_Data\<close>\<open>(spec)\<close> is analogous to \<^ML_functor>\<open>Theory_Data\<close> for type \<^ML_type>\<open>Context.generic\<close>. \<close>

text %mlex \<open>
  The following artificial example demonstrates theory data: we maintain a set
  of terms that are supposed to be wellformed wrt.\ the enclosing theory. The
  public interface is as follows:
\<close>

ML \<open>
  signature WELLFORMED_TERMS =
  sig
    val get: theory -> term list
    val add: term -> theory -> theory
  end;
\<close>

text \<open>
  The implementation uses private theory data internally, and only exposes an
  operation that involves explicit argument checking wrt.\ the given theory.
\<close>

ML \<open>
  structure Wellformed_Terms: WELLFORMED_TERMS =
  struct

  structure Terms = Theory_Data
  (
    type T = term Ord_List.T;
    val empty = [];
    val extend = I;
    fun merge (ts1, ts2) =
      Ord_List.union Term_Ord.fast_term_ord ts1 ts2;
  );

  val get = Terms.get;

  fun add raw_t thy =
    let
      val t = Sign.cert_term thy raw_t;
    in
      Terms.map (Ord_List.insert Term_Ord.fast_term_ord t) thy
    end;

  end;
\<close>

text \<open>
  Type \<^ML_type>\<open>term Ord_List.T\<close> is used for reasonably efficient
  representation of a set of terms: all operations are linear in the number of
  stored elements. Here we assume that users of this module do not care about
  the declaration order, since that data structure forces its own arrangement
  of elements.

  Observe how the \<^ML_text>\<open>merge\<close> operation joins the data slots of the two
  constituents: \<^ML>\<open>Ord_List.union\<close> prevents duplication of common data from
  different branches, thus avoiding the danger of exponential blowup. Plain
  list append etc.\ must never be used for theory data merges!

  \<^medskip>
  Our intended invariant is achieved as follows:

    \<^enum> \<^ML>\<open>Wellformed_Terms.add\<close> only admits terms that have passed the \<^ML>\<open>Sign.cert_term\<close> check of the given theory at that point.
  
    \<^enum> Wellformedness in the sense of \<^ML>\<open>Sign.cert_term\<close> is monotonic wrt.\
    the sub-theory relation. So our data can move upwards in the hierarchy
    (via extension or merges), and maintain wellformedness without further
    checks.

  Note that all basic operations of the inference kernel (which includes \<^ML>\<open>Sign.cert_term\<close>) observe this monotonicity principle, but other user-space
  tools don't. For example, fully-featured type-inference via \<^ML>\<open>Syntax.check_term\<close> (cf.\ \secref{sec:term-check}) is not necessarily
  monotonic wrt.\ the background theory, since constraints of term constants
  can be modified by later declarations, for example.

  In most cases, user-space context data does not have to take such invariants
  too seriously. The situation is different in the implementation of the
  inference kernel itself, which uses the very same data mechanisms for types,
  constants, axioms etc.
\<close>


subsection \<open>Configuration options \label{sec:config-options}\<close>

text \<open>
  A \<^emph>\<open>configuration option\<close> is a named optional value of some basic type
  (Boolean, integer, string) that is stored in the context. It is a simple
  application of general context data (\secref{sec:context-data}) that is
  sufficiently common to justify customized setup, which includes some
  concrete declarations for end-users using existing notation for attributes
  (cf.\ \secref{sec:attributes}).

  For example, the predefined configuration option @{attribute show_types}
  controls output of explicit type constraints for variables in printed terms
  (cf.\ \secref{sec:read-print}). Its value can be modified within Isar text
  like this:
\<close>

experiment
begin

declare [[show_types = false]]
  \<comment> \<open>declaration within (local) theory context\<close>

notepad
begin
  note [[show_types = true]]
    \<comment> \<open>declaration within proof (forward mode)\<close>
  term x

  have "x = x"
    using [[show_types = false]]
      \<comment> \<open>declaration within proof (backward mode)\<close>
    ..
end

end

text \<open>
  Configuration options that are not set explicitly hold a default value that
  can depend on the application context. This allows to retrieve the value
  from another slot within the context, or fall back on a global preference
  mechanism, for example.

  The operations to declare configuration options and get/map their values are
  modeled as direct replacements for historic global references, only that the
  context is made explicit. This allows easy configuration of tools, without
  relying on the execution order as required for old-style mutable
  references.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Config.get: "Proof.context -> 'a Config.T -> 'a"} \\
  @{index_ML Config.map: "'a Config.T -> ('a -> 'a) -> Proof.context -> Proof.context"} \\
  @{index_ML Attrib.setup_config_bool: "binding -> (Context.generic -> bool) ->
  bool Config.T"} \\
  @{index_ML Attrib.setup_config_int: "binding -> (Context.generic -> int) ->
  int Config.T"} \\
  @{index_ML Attrib.setup_config_real: "binding -> (Context.generic -> real) ->
  real Config.T"} \\
  @{index_ML Attrib.setup_config_string: "binding -> (Context.generic -> string) ->
  string Config.T"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Config.get\<close>~\<open>ctxt config\<close> gets the value of \<open>config\<close> in the given
  context.

  \<^descr> \<^ML>\<open>Config.map\<close>~\<open>config f ctxt\<close> updates the context by updating the value
  of \<open>config\<close>.

  \<^descr> \<open>config =\<close>~\<^ML>\<open>Attrib.setup_config_bool\<close>~\<open>name default\<close> creates a named
  configuration option of type \<^ML_type>\<open>bool\<close>, with the given \<open>default\<close>
  depending on the application context. The resulting \<open>config\<close> can be used to
  get/map its value in a given context. There is an implicit update of the
  background theory that registers the option as attribute with some concrete
  syntax.

  \<^descr> \<^ML>\<open>Attrib.config_int\<close>, \<^ML>\<open>Attrib.config_real\<close>, and \<^ML>\<open>Attrib.config_string\<close> work like \<^ML>\<open>Attrib.config_bool\<close>, but for types
  \<^ML_type>\<open>int\<close> and \<^ML_type>\<open>string\<close>, respectively.
\<close>

text %mlex \<open>
  The following example shows how to declare and use a Boolean configuration
  option called \<open>my_flag\<close> with constant default value \<^ML>\<open>false\<close>.
\<close>

ML \<open>
  val my_flag =
    Attrib.setup_config_bool \<^binding>\<open>my_flag\<close> (K false)
\<close>

text \<open>
  Now the user can refer to @{attribute my_flag} in declarations, while ML
  tools can retrieve the current value from the context via \<^ML>\<open>Config.get\<close>.
\<close>

ML_val \<open>\<^assert> (Config.get \<^context> my_flag = false)\<close>

declare [[my_flag = true]]

ML_val \<open>\<^assert> (Config.get \<^context> my_flag = true)\<close>

notepad
begin
  {
    note [[my_flag = false]]
    ML_val \<open>\<^assert> (Config.get \<^context> my_flag = false)\<close>
  }
  ML_val \<open>\<^assert> (Config.get \<^context> my_flag = true)\<close>
end

text \<open>
  Here is another example involving ML type \<^ML_type>\<open>real\<close> (floating-point
  numbers).
\<close>

ML \<open>
  val airspeed_velocity =
    Attrib.setup_config_real \<^binding>\<open>airspeed_velocity\<close> (K 0.0)
\<close>

declare [[airspeed_velocity = 10]]
declare [[airspeed_velocity = 9.9]]


section \<open>Names \label{sec:names}\<close>

text \<open>
  In principle, a name is just a string, but there are various conventions for
  representing additional structure. For example, ``\<open>Foo.bar.baz\<close>'' is
  considered as a long name consisting of qualifier \<open>Foo.bar\<close> and base name
  \<open>baz\<close>. The individual constituents of a name may have further substructure,
  e.g.\ the string ``\<^verbatim>\<open>\<alpha>\<close>'' encodes as a single symbol (\secref{sec:symbols}).

  \<^medskip>
  Subsequently, we shall introduce specific categories of names. Roughly
  speaking these correspond to logical entities as follows:

  \<^item> Basic names (\secref{sec:basic-name}): free and bound variables.

  \<^item> Indexed names (\secref{sec:indexname}): schematic variables.

  \<^item> Long names (\secref{sec:long-name}): constants of any kind (type
  constructors, term constants, other concepts defined in user space). Such
  entities are typically managed via name spaces (\secref{sec:name-space}).
\<close>


subsection \<open>Basic names \label{sec:basic-name}\<close>

text \<open>
  A \<^emph>\<open>basic name\<close> essentially consists of a single Isabelle identifier. There
  are conventions to mark separate classes of basic names, by attaching a
  suffix of underscores: one underscore means \<^emph>\<open>internal name\<close>, two
  underscores means \<^emph>\<open>Skolem name\<close>, three underscores means \<^emph>\<open>internal Skolem
  name\<close>.

  For example, the basic name \<open>foo\<close> has the internal version \<open>foo_\<close>, with
  Skolem versions \<open>foo__\<close> and \<open>foo___\<close>, respectively.

  These special versions provide copies of the basic name space, apart from
  anything that normally appears in the user text. For example, system
  generated variables in Isar proof contexts are usually marked as internal,
  which prevents mysterious names like \<open>xaa\<close> to appear in human-readable text.

  \<^medskip>
  Manipulating binding scopes often requires on-the-fly renamings. A \<^emph>\<open>name
  context\<close> contains a collection of already used names. The \<open>declare\<close>
  operation adds names to the context.

  The \<open>invents\<close> operation derives a number of fresh names from a given
  starting point. For example, the first three names derived from \<open>a\<close> are \<open>a\<close>,
  \<open>b\<close>, \<open>c\<close>.

  The \<open>variants\<close> operation produces fresh names by incrementing tentative
  names as base-26 numbers (with digits \<open>a..z\<close>) until all clashes are
  resolved. For example, name \<open>foo\<close> results in variants \<open>fooa\<close>, \<open>foob\<close>,
  \<open>fooc\<close>, \dots, \<open>fooaa\<close>, \<open>fooab\<close> etc.; each renaming step picks the next
  unused variant from this sequence.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Name.internal: "string -> string"} \\
  @{index_ML Name.skolem: "string -> string"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name.context} \\
  @{index_ML Name.context: Name.context} \\
  @{index_ML Name.declare: "string -> Name.context -> Name.context"} \\
  @{index_ML Name.invent: "Name.context -> string -> int -> string list"} \\
  @{index_ML Name.variant: "string -> Name.context -> string * Name.context"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML Variable.names_of: "Proof.context -> Name.context"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Name.internal\<close>~\<open>name\<close> produces an internal name by adding one
  underscore.

  \<^descr> \<^ML>\<open>Name.skolem\<close>~\<open>name\<close> produces a Skolem name by adding two underscores.

  \<^descr> Type \<^ML_type>\<open>Name.context\<close> represents the context of already used names;
  the initial value is \<^ML>\<open>Name.context\<close>.

  \<^descr> \<^ML>\<open>Name.declare\<close>~\<open>name\<close> enters a used name into the context.

  \<^descr> \<^ML>\<open>Name.invent\<close>~\<open>context name n\<close> produces \<open>n\<close> fresh names derived from
  \<open>name\<close>.

  \<^descr> \<^ML>\<open>Name.variant\<close>~\<open>name context\<close> produces a fresh variant of \<open>name\<close>; the
  result is declared to the context.

  \<^descr> \<^ML>\<open>Variable.names_of\<close>~\<open>ctxt\<close> retrieves the context of declared type and
  term variable names. Projecting a proof context down to a primitive name
  context is occasionally useful when invoking lower-level operations. Regular
  management of ``fresh variables'' is done by suitable operations of
  structure \<^ML_structure>\<open>Variable\<close>, which is also able to provide an
  official status of ``locally fixed variable'' within the logical environment
  (cf.\ \secref{sec:variables}).
\<close>

text %mlex \<open>
  The following simple examples demonstrate how to produce fresh names from
  the initial \<^ML>\<open>Name.context\<close>.
\<close>

ML_val \<open>
  val list1 = Name.invent Name.context "a" 5;
  \<^assert> (list1 = ["a", "b", "c", "d", "e"]);

  val list2 =
    #1 (fold_map Name.variant ["x", "x", "a", "a", "'a", "'a"] Name.context);
  \<^assert> (list2 = ["x", "xa", "a", "aa", "'a", "'aa"]);
\<close>

text \<open>
  \<^medskip>
  The same works relatively to the formal context as follows.\<close>

experiment fixes a b c :: 'a
begin

ML_val \<open>
  val names = Variable.names_of \<^context>;

  val list1 = Name.invent names "a" 5;
  \<^assert> (list1 = ["d", "e", "f", "g", "h"]);

  val list2 =
    #1 (fold_map Name.variant ["x", "x", "a", "a", "'a", "'a"] names);
  \<^assert> (list2 = ["x", "xa", "aa", "ab", "'aa", "'ab"]);
\<close>

end


subsection \<open>Indexed names \label{sec:indexname}\<close>

text \<open>
  An \<^emph>\<open>indexed name\<close> (or \<open>indexname\<close>) is a pair of a basic name and a natural
  number. This representation allows efficient renaming by incrementing the
  second component only. The canonical way to rename two collections of
  indexnames apart from each other is this: determine the maximum index
  \<open>maxidx\<close> of the first collection, then increment all indexes of the second
  collection by \<open>maxidx + 1\<close>; the maximum index of an empty collection is
  \<open>-1\<close>.

  Occasionally, basic names are injected into the same pair type of indexed
  names: then \<open>(x, -1)\<close> is used to encode the basic name \<open>x\<close>.

  \<^medskip>
  Isabelle syntax observes the following rules for representing an indexname
  \<open>(x, i)\<close> as a packed string:

    \<^item> \<open>?x\<close> if \<open>x\<close> does not end with a digit and \<open>i = 0\<close>,

    \<^item> \<open>?xi\<close> if \<open>x\<close> does not end with a digit,

    \<^item> \<open>?x.i\<close> otherwise.

  Indexnames may acquire large index numbers after several maxidx shifts have
  been applied. Results are usually normalized towards \<open>0\<close> at certain
  checkpoints, notably at the end of a proof. This works by producing variants
  of the corresponding basic name components. For example, the collection
  \<open>?x1, ?x7, ?x42\<close> becomes \<open>?x, ?xa, ?xb\<close>.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type indexname = "string * int"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>indexname\<close> represents indexed names. This is an
  abbreviation for \<^ML_type>\<open>string * int\<close>. The second component is usually
  non-negative, except for situations where \<open>(x, -1)\<close> is used to inject basic
  names into this type. Other negative indexes should not be used.
\<close>


subsection \<open>Long names \label{sec:long-name}\<close>

text \<open>
  A \<^emph>\<open>long name\<close> consists of a sequence of non-empty name components. The
  packed representation uses a dot as separator, as in ``\<open>A.b.c\<close>''. The last
  component is called \<^emph>\<open>base name\<close>, the remaining prefix is called
  \<^emph>\<open>qualifier\<close> (which may be empty). The qualifier can be understood as the
  access path to the named entity while passing through some nested
  block-structure, although our free-form long names do not really enforce any
  strict discipline.

  For example, an item named ``\<open>A.b.c\<close>'' may be understood as a local entity
  \<open>c\<close>, within a local structure \<open>b\<close>, within a global structure \<open>A\<close>. In
  practice, long names usually represent 1--3 levels of qualification. User ML
  code should not make any assumptions about the particular structure of long
  names!

  The empty name is commonly used as an indication of unnamed entities, or
  entities that are not entered into the corresponding name space, whenever
  this makes any sense. The basic operations on long names map empty names
  again to empty names.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Long_Name.base_name: "string -> string"} \\
  @{index_ML Long_Name.qualifier: "string -> string"} \\
  @{index_ML Long_Name.append: "string -> string -> string"} \\
  @{index_ML Long_Name.implode: "string list -> string"} \\
  @{index_ML Long_Name.explode: "string -> string list"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Long_Name.base_name\<close>~\<open>name\<close> returns the base name of a long name.

  \<^descr> \<^ML>\<open>Long_Name.qualifier\<close>~\<open>name\<close> returns the qualifier of a long name.

  \<^descr> \<^ML>\<open>Long_Name.append\<close>~\<open>name\<^sub>1 name\<^sub>2\<close> appends two long names.

  \<^descr> \<^ML>\<open>Long_Name.implode\<close>~\<open>names\<close> and \<^ML>\<open>Long_Name.explode\<close>~\<open>name\<close> convert
  between the packed string representation and the explicit list form of long
  names.
\<close>


subsection \<open>Name spaces \label{sec:name-space}\<close>

text \<open>
  A \<open>name space\<close> manages a collection of long names, together with a mapping
  between partially qualified external names and fully qualified internal
  names (in both directions). Note that the corresponding \<open>intern\<close> and
  \<open>extern\<close> operations are mostly used for parsing and printing only! The
  \<open>declare\<close> operation augments a name space according to the accesses
  determined by a given binding, and a naming policy from the context.

  \<^medskip>
  A \<open>binding\<close> specifies details about the prospective long name of a newly
  introduced formal entity. It consists of a base name, prefixes for
  qualification (separate ones for system infrastructure and user-space
  mechanisms), a slot for the original source position, and some additional
  flags.

  \<^medskip>
  A \<open>naming\<close> provides some additional details for producing a long name from a
  binding. Normally, the naming is implicit in the theory or proof context.
  The \<open>full\<close> operation (and its variants for different context types) produces
  a fully qualified internal name to be entered into a name space. The main
  equation of this ``chemical reaction'' when binding new entities in a
  context is as follows:

  \<^medskip>
  \begin{tabular}{l}
  \<open>binding + naming \<longrightarrow> long name + name space accesses\<close>
  \end{tabular}

  \<^bigskip>
  As a general principle, there is a separate name space for each kind of
  formal entity, e.g.\ fact, logical constant, type constructor, type class.
  It is usually clear from the occurrence in concrete syntax (or from the
  scope) which kind of entity a name refers to. For example, the very same
  name \<open>c\<close> may be used uniformly for a constant, type constructor, and type
  class.

  There are common schemes to name derived entities systematically according
  to the name of the main logical entity involved, e.g.\ fact \<open>c.intro\<close> for a
  canonical introduction rule related to constant \<open>c\<close>. This technique of
  mapping names from one space into another requires some care in order to
  avoid conflicts. In particular, theorem names derived from a type
  constructor or type class should get an additional suffix in addition to the
  usual qualification. This leads to the following conventions for derived
  names:

  \<^medskip>
  \begin{tabular}{ll}
  logical entity & fact name \\\hline
  constant \<open>c\<close> & \<open>c.intro\<close> \\
  type \<open>c\<close> & \<open>c_type.intro\<close> \\
  class \<open>c\<close> & \<open>c_class.intro\<close> \\
  \end{tabular}
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type binding} \\
  @{index_ML Binding.empty: binding} \\
  @{index_ML Binding.name: "string -> binding"} \\
  @{index_ML Binding.qualify: "bool -> string -> binding -> binding"} \\
  @{index_ML Binding.prefix: "bool -> string -> binding -> binding"} \\
  @{index_ML Binding.concealed: "binding -> binding"} \\
  @{index_ML Binding.print: "binding -> string"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name_Space.naming} \\
  @{index_ML Name_Space.global_naming: Name_Space.naming} \\
  @{index_ML Name_Space.add_path: "string -> Name_Space.naming -> Name_Space.naming"} \\
  @{index_ML Name_Space.full_name: "Name_Space.naming -> binding -> string"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML_type Name_Space.T} \\
  @{index_ML Name_Space.empty: "string -> Name_Space.T"} \\
  @{index_ML Name_Space.merge: "Name_Space.T * Name_Space.T -> Name_Space.T"} \\
  @{index_ML Name_Space.declare: "Context.generic -> bool ->
  binding -> Name_Space.T -> string * Name_Space.T"} \\
  @{index_ML Name_Space.intern: "Name_Space.T -> string -> string"} \\
  @{index_ML Name_Space.extern: "Proof.context -> Name_Space.T -> string -> string"} \\
  @{index_ML Name_Space.is_concealed: "Name_Space.T -> string -> bool"}
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>binding\<close> represents the abstract concept of name bindings.

  \<^descr> \<^ML>\<open>Binding.empty\<close> is the empty binding.

  \<^descr> \<^ML>\<open>Binding.name\<close>~\<open>name\<close> produces a binding with base name \<open>name\<close>. Note
  that this lacks proper source position information; see also the ML
  antiquotation @{ML_antiquotation binding}.

  \<^descr> \<^ML>\<open>Binding.qualify\<close>~\<open>mandatory name binding\<close> prefixes qualifier \<open>name\<close>
  to \<open>binding\<close>. The \<open>mandatory\<close> flag tells if this name component always needs
  to be given in name space accesses --- this is mostly \<open>false\<close> in practice.
  Note that this part of qualification is typically used in derived
  specification mechanisms.

  \<^descr> \<^ML>\<open>Binding.prefix\<close> is similar to \<^ML>\<open>Binding.qualify\<close>, but affects the
  system prefix. This part of extra qualification is typically used in the
  infrastructure for modular specifications, notably ``local theory targets''
  (see also \chref{ch:local-theory}).

  \<^descr> \<^ML>\<open>Binding.concealed\<close>~\<open>binding\<close> indicates that the binding shall refer
  to an entity that serves foundational purposes only. This flag helps to mark
  implementation details of specification mechanism etc. Other tools should
  not depend on the particulars of concealed entities (cf.\ \<^ML>\<open>Name_Space.is_concealed\<close>).

  \<^descr> \<^ML>\<open>Binding.print\<close>~\<open>binding\<close> produces a string representation for
  human-readable output, together with some formal markup that might get used
  in GUI front-ends, for example.

  \<^descr> Type \<^ML_type>\<open>Name_Space.naming\<close> represents the abstract concept of a
  naming policy.

  \<^descr> \<^ML>\<open>Name_Space.global_naming\<close> is the default naming policy: it is global
  and lacks any path prefix. In a regular theory context this is augmented by
  a path prefix consisting of the theory name.

  \<^descr> \<^ML>\<open>Name_Space.add_path\<close>~\<open>path naming\<close> augments the naming policy by
  extending its path component.

  \<^descr> \<^ML>\<open>Name_Space.full_name\<close>~\<open>naming binding\<close> turns a name binding (usually
  a basic name) into the fully qualified internal name, according to the given
  naming policy.

  \<^descr> Type \<^ML_type>\<open>Name_Space.T\<close> represents name spaces.

  \<^descr> \<^ML>\<open>Name_Space.empty\<close>~\<open>kind\<close> and \<^ML>\<open>Name_Space.merge\<close>~\<open>(space\<^sub>1,
  space\<^sub>2)\<close> are the canonical operations for maintaining name spaces according
  to theory data management (\secref{sec:context-data}); \<open>kind\<close> is a formal
  comment to characterize the purpose of a name space.

  \<^descr> \<^ML>\<open>Name_Space.declare\<close>~\<open>context strict binding space\<close> enters a name
  binding as fully qualified internal name into the name space, using the
  naming of the context.

  \<^descr> \<^ML>\<open>Name_Space.intern\<close>~\<open>space name\<close> internalizes a (partially qualified)
  external name.

  This operation is mostly for parsing! Note that fully qualified names
  stemming from declarations are produced via \<^ML>\<open>Name_Space.full_name\<close> and
  \<^ML>\<open>Name_Space.declare\<close> (or their derivatives for \<^ML_type>\<open>theory\<close> and
  \<^ML_type>\<open>Proof.context\<close>).

  \<^descr> \<^ML>\<open>Name_Space.extern\<close>~\<open>ctxt space name\<close> externalizes a (fully qualified)
  internal name.

  This operation is mostly for printing! User code should not rely on the
  precise result too much.

  \<^descr> \<^ML>\<open>Name_Space.is_concealed\<close>~\<open>space name\<close> indicates whether \<open>name\<close> refers
  to a strictly private entity that other tools are supposed to ignore!
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "binding"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation binding} embedded
  \<close>

  \<^descr> \<open>@{binding name}\<close> produces a binding with base name \<open>name\<close> and the source
  position taken from the concrete syntax of this antiquotation. In many
  situations this is more appropriate than the more basic \<^ML>\<open>Binding.name\<close>
  function.
\<close>

text %mlex \<open>
  The following example yields the source position of some concrete binding
  inlined into the text:
\<close>

ML_val \<open>Binding.pos_of \<^binding>\<open>here\<close>\<close>

text \<open>
  \<^medskip>
  That position can be also printed in a message as follows:
\<close>

ML_command
  \<open>writeln
    ("Look here" ^ Position.here (Binding.pos_of \<^binding>\<open>here\<close>))\<close>

text \<open>
  This illustrates a key virtue of formalized bindings as opposed to raw
  specifications of base names: the system can use this additional information
  for feedback given to the user (error messages etc.).

  \<^medskip>
  The following example refers to its source position directly, which is
  occasionally useful for experimentation and diagnostic purposes:
\<close>

ML_command \<open>warning ("Look here" ^ Position.here \<^here>)\<close>

end
