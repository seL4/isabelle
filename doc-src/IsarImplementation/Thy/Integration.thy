theory Integration
imports Base
begin

chapter {* System integration *}

section {* Isar toplevel \label{sec:isar-toplevel} *}

text {* The Isar toplevel may be considered the centeral hub of the
  Isabelle/Isar system, where all key components and sub-systems are
  integrated into a single read-eval-print loop of Isar commands,
  which also incorporates the underlying ML compiler.

  Isabelle/Isar departs from the original ``LCF system architecture''
  where ML was really The Meta Language for defining theories and
  conducting proofs.  Instead, ML now only serves as the
  implementation language for the system (and user extensions), while
  the specific Isar toplevel supports the concepts of theory and proof
  development natively.  This includes the graph structure of theories
  and the block structure of proofs, support for unlimited undo,
  facilities for tracing, debugging, timing, profiling etc.

  \medskip The toplevel maintains an implicit state, which is
  transformed by a sequence of transitions -- either interactively or
  in batch-mode.  In interactive mode, Isar state transitions are
  encapsulated as safe transactions, such that both failure and undo
  are handled conveniently without destroying the underlying draft
  theory (cf.~\secref{sec:context-theory}).  In batch mode,
  transitions operate in a linear (destructive) fashion, such that
  error conditions abort the present attempt to construct a theory or
  proof altogether.

  The toplevel state is a disjoint sum of empty @{text toplevel}, or
  @{text theory}, or @{text proof}.  On entering the main Isar loop we
  start with an empty toplevel.  A theory is commenced by giving a
  @{text \<THEORY>} header; within a theory we may issue theory
  commands such as @{text \<DEFINITION>}, or state a @{text
  \<THEOREM>} to be proven.  Now we are within a proof state, with a
  rich collection of Isar proof commands for structured proof
  composition, or unstructured proof scripts.  When the proof is
  concluded we get back to the theory, which is then updated by
  storing the resulting fact.  Further theory declarations or theorem
  statements with proofs may follow, until we eventually conclude the
  theory development by issuing @{text \<END>}.  The resulting theory
  is then stored within the theory database and we are back to the
  empty toplevel.

  In addition to these proper state transformations, there are also
  some diagnostic commands for peeking at the toplevel state without
  modifying it (e.g.\ \isakeyword{thm}, \isakeyword{term},
  \isakeyword{print-cases}).
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Toplevel.state} \\
  @{index_ML Toplevel.UNDEF: "exn"} \\
  @{index_ML Toplevel.is_toplevel: "Toplevel.state -> bool"} \\
  @{index_ML Toplevel.theory_of: "Toplevel.state -> theory"} \\
  @{index_ML Toplevel.proof_of: "Toplevel.state -> Proof.state"} \\
  @{index_ML Toplevel.debug: "bool Unsynchronized.ref"} \\
  @{index_ML Toplevel.timing: "bool Unsynchronized.ref"} \\
  @{index_ML Toplevel.profiling: "int Unsynchronized.ref"} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type Toplevel.state} represents Isar toplevel
  states, which are normally manipulated through the concept of
  toplevel transitions only (\secref{sec:toplevel-transition}).  Also
  note that a raw toplevel state is subject to the same linearity
  restrictions as a theory context (cf.~\secref{sec:context-theory}).

  \item @{ML Toplevel.UNDEF} is raised for undefined toplevel
  operations.  Many operations work only partially for certain cases,
  since @{ML_type Toplevel.state} is a sum type.

  \item @{ML Toplevel.is_toplevel}~@{text "state"} checks for an empty
  toplevel state.

  \item @{ML Toplevel.theory_of}~@{text "state"} selects the
  background theory of @{text "state"}, raises @{ML Toplevel.UNDEF}
  for an empty toplevel state.

  \item @{ML Toplevel.proof_of}~@{text "state"} selects the Isar proof
  state if available, otherwise raises @{ML Toplevel.UNDEF}.

  \item @{ML "Toplevel.debug := true"} makes the toplevel print further
  details about internal error conditions, exceptions being raised
  etc.

  \item @{ML "Toplevel.timing := true"} makes the toplevel print timing
  information for each Isar command being executed.

  \item @{ML Toplevel.profiling}~@{ML_text ":="}~@{text "n"} controls
  low-level profiling of the underlying ML runtime system.  For
  Poly/ML, @{text "n = 1"} means time and @{text "n = 2"} space
  profiling.

  \end{description}
*}

text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "Isar.state"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  \begin{description}

  \item @{text "@{Isar.state}"} refers to Isar toplevel state at that
  point --- as abstract value.

  This only works for diagnostic ML commands, such as @{command
  ML_val} or @{command ML_command}.

  \end{description}
*}


subsection {* Toplevel transitions \label{sec:toplevel-transition} *}

text {*
  An Isar toplevel transition consists of a partial function on the
  toplevel state, with additional information for diagnostics and
  error reporting: there are fields for command name, source position,
  optional source text, as well as flags for interactive-only commands
  (which issue a warning in batch-mode), printing of result state,
  etc.

  The operational part is represented as the sequential union of a
  list of partial functions, which are tried in turn until the first
  one succeeds.  This acts like an outer case-expression for various
  alternative state transitions.  For example, \isakeyword{qed} works
  differently for a local proofs vs.\ the global ending of the main
  proof.

  Toplevel transitions are composed via transition transformers.
  Internally, Isar commands are put together from an empty transition
  extended by name and source position.  It is then left to the
  individual command parser to turn the given concrete syntax into a
  suitable transition transformer that adjoins actual operations on a
  theory or proof state etc.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Toplevel.print: "Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.no_timing: "Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.keep: "(Toplevel.state -> unit) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.theory: "(theory -> theory) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.theory_to_proof: "(theory -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.proof: "(Proof.state -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.proofs: "(Proof.state -> Proof.state Seq.seq) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.end_proof: "(bool -> Proof.state -> Proof.context) ->
  Toplevel.transition -> Toplevel.transition"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Toplevel.print}~@{text "tr"} sets the print flag, which
  causes the toplevel loop to echo the result state (in interactive
  mode).

  \item @{ML Toplevel.no_timing}~@{text "tr"} indicates that the
  transition should never show timing information, e.g.\ because it is
  a diagnostic command.

  \item @{ML Toplevel.keep}~@{text "tr"} adjoins a diagnostic
  function.

  \item @{ML Toplevel.theory}~@{text "tr"} adjoins a theory
  transformer.

  \item @{ML Toplevel.theory_to_proof}~@{text "tr"} adjoins a global
  goal function, which turns a theory into a proof state.  The theory
  may be changed before entering the proof; the generic Isar goal
  setup includes an argument that specifies how to apply the proven
  result to the theory, when the proof is finished.

  \item @{ML Toplevel.proof}~@{text "tr"} adjoins a deterministic
  proof command, with a singleton result.

  \item @{ML Toplevel.proofs}~@{text "tr"} adjoins a general proof
  command, with zero or more result states (represented as a lazy
  list).

  \item @{ML Toplevel.end_proof}~@{text "tr"} adjoins a concluding
  proof command, that returns the resulting theory, after storing the
  resulting facts in the context etc.

  \end{description}
*}


section {* Theory database \label{sec:theory-database} *}

text {*
  The theory database maintains a collection of theories, together
  with some administrative information about their original sources,
  which are held in an external store (i.e.\ some directory within the
  regular file system).

  The theory database is organized as a directed acyclic graph;
  entries are referenced by theory name.  Although some additional
  interfaces allow to include a directory specification as well, this
  is only a hint to the underlying theory loader.  The internal theory
  name space is flat!

  Theory @{text A} is associated with the main theory file @{text
  A}\verb,.thy,, which needs to be accessible through the theory
  loader path.  Any number of additional ML source files may be
  associated with each theory, by declaring these dependencies in the
  theory header as @{text \<USES>}, and loading them consecutively
  within the theory context.  The system keeps track of incoming ML
  sources and associates them with the current theory.

  The basic internal actions of the theory database are @{text
  "update"} and @{text "remove"}:

  \begin{itemize}

  \item @{text "update A"} introduces a link of @{text "A"} with a
  @{text "theory"} value of the same name; it asserts that the theory
  sources are now consistent with that value;

  \item @{text "remove A"} deletes entry @{text "A"} from the theory
  database.
  
  \end{itemize}

  These actions are propagated to sub- or super-graphs of a theory
  entry as expected, in order to preserve global consistency of the
  state of all loaded theories with the sources of the external store.
  This implies certain causalities between actions: @{text "update"}
  or @{text "remove"} of an entry will @{text "remove"} all
  descendants.

  \medskip There are separate user-level interfaces to operate on the
  theory database directly or indirectly.  The primitive actions then
  just happen automatically while working with the system.  In
  particular, processing a theory header @{text "\<THEORY> A
  \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>"} ensures that the
  sub-graph of the collective imports @{text "B\<^sub>1 \<dots> B\<^sub>n"}
  is up-to-date, too.  Earlier theories are reloaded as required, with
  @{text update} actions proceeding in topological order according to
  theory dependencies.  There may be also a wave of implied @{text
  remove} actions for derived theory nodes until a stable situation
  is achieved eventually.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML use_thy: "string -> unit"} \\
  @{index_ML use_thys: "string list -> unit"} \\
  @{index_ML Thy_Info.get_theory: "string -> theory"} \\
  @{index_ML Thy_Info.remove_thy: "string -> unit"} \\[1ex]
  @{index_ML Thy_Info.register_thy: "theory -> unit"} \\[1ex]
  @{ML_text "datatype action = Update | Remove"} \\
  @{index_ML Thy_Info.add_hook: "(Thy_Info.action -> string -> unit) -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML use_thy}~@{text A} ensures that theory @{text A} is fully
  up-to-date wrt.\ the external file store, reloading outdated
  ancestors as required.  In batch mode, the simultaneous @{ML
  use_thys} should be used exclusively.

  \item @{ML use_thys} is similar to @{ML use_thy}, but handles
  several theories simultaneously.  Thus it acts like processing the
  import header of a theory, without performing the merge of the
  result.  By loading a whole sub-graph of theories like that, the
  intrinsic parallelism can be exploited by the system, to speedup
  loading.

  \item @{ML Thy_Info.get_theory}~@{text A} retrieves the theory value
  presently associated with name @{text A}.  Note that the result
  might be outdated.

  \item @{ML Thy_Info.remove_thy}~@{text A} deletes theory @{text A} and all
  descendants from the theory database.

  \item @{ML Thy_Info.register_thy}~@{text "text thy"} registers an
  existing theory value with the theory loader database and updates
  source version information according to the current file-system
  state.

  \item @{ML "Thy_Info.add_hook"}~@{text f} registers function @{text
  f} as a hook for theory database actions.  The function will be
  invoked with the action and theory name being involved; thus derived
  actions may be performed in associated system components, e.g.\
  maintaining the state of an editor for the theory sources.

  The kind and order of actions occurring in practice depends both on
  user interactions and the internal process of resolving theory
  imports.  Hooks should not rely on a particular policy here!  Any
  exceptions raised by the hook are ignored.

  \end{description}
*}

end
