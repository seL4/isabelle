
(* $Id$ *)

theory integration imports base begin

chapter {* System integration *}

section {* Isar toplevel *}

text {* The Isar toplevel may be considered the centeral hub of the
  Isabelle/Isar system, where all key components and sub-systems are
  integrated into a single read-eval-print loop of Isar commands.
  Here we even incorporate the existing {\ML} toplevel of the compiler
  and run-time system (cf.\ \secref{sec:ML-toplevel}).

  Isabelle/Isar departs from original ``LCF system architecture''
  where {\ML} was really The Meta Language for defining theories and
  conducting proofs.  Instead, {\ML} merely serves as the
  implementation language for the system (and user extensions), while
  our specific Isar toplevel supports particular notions of
  incremental theory and proof development more directly.  This
  includes the graph structure of theories and the block structure of
  proofs, support for unlimited undo, facilities for tracing,
  debugging, timing, profiling.

  \medskip The toplevel maintains an implicit state, which is
  transformed by a sequence of transitions -- either interactively or
  in batch-mode.  In interactive mode, Isar state transitions are
  encapsulated as safe transactions, such that both failure and undo
  are handled conveniently without destroying the underlying draft
  theory (cf.~\secref{sec:context-theory}).  In batch mode,
  transitions operate in a strictly linear (destructive) fashion, such
  that error conditions abort the present attempt to construct a
  theory altogether.

  The toplevel state is a disjoint sum of empty @{text toplevel}, or
  @{text theory}, or @{text proof}.  On entering the main Isar loop we
  start with an empty toplevel.  A theory is commenced by giving a
  @{text \<THEORY>} header; within a theory we may issue theory
  commands such as @{text \<CONSTS>} or @{text \<DEFS>}, or state a
  @{text \<THEOREM>} to be proven.  Now we are within a proof state,
  with a rich collection of Isar proof commands for structured proof
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
  @{index_ML Toplevel.debug: "bool ref"} \\
  @{index_ML Toplevel.timing: "bool ref"} \\
  @{index_ML Toplevel.profiling: "int ref"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML_type Toplevel.state} represents Isar toplevel states,
  which are normally only manipulated through the toplevel transition
  concept (\secref{sec:toplevel-transition}).  Also note that a
  toplevel state is subject to the same linerarity restrictions as a
  theory context (cf.~\secref{sec:context-theory}).

  \item @{ML Toplevel.UNDEF} is raised for undefined toplevel
  operations: @{ML_type Toplevel.state} is a sum type, many operations
  work only partially for certain cases.

  \item @{ML Toplevel.is_toplevel} checks for an empty toplevel state.

  \item @{ML Toplevel.theory_of} gets the theory of a theory or proof
  (!), otherwise raises @{ML Toplevel.UNDEF}.

  \item @{ML Toplevel.proof_of} gets the Isar proof state if
  available, otherwise raises @{ML Toplevel.UNDEF}.

  \item @{ML "set Toplevel.debug"} makes the toplevel print further
  details about internal error conditions, exceptions being raised
  etc.

  \item @{ML "set Toplevel.timing"} makes the toplevel print timing
  information for each Isar command being executed.

  \item @{ML Toplevel.profiling} controls low-level profiling of the
  underlying {\ML} runtime system.\footnote{For Poly/ML, 1 means time
  and 2 space profiling.}

  \end{description}
*}


subsection {* Toplevel transitions *}

text {* An Isar toplevel transition consists of a partial
  function on the toplevel state, with additional information for
  diagnostics and error reporting: there are fields for command name,
  source position, optional source text, as well as flags for
  interactive-only commands (which issue a warning in batch-mode),
  printing of result state, etc.

  The operational part is represented as a sequential union of a list
  of partial functions, which are tried in turn until the first one
  succeeds (i.e.\ does not raise @{ML Toplevel.UNDEF}).  For example,
  a single Isar command like \isacommand{qed} consists of the union of
  some function @{ML_type "Proof.state -> Proof.state"} for proofs
  within proofs, plus @{ML_type "Proof.state -> theory"} for proofs at
  the outer theory level.

  Toplevel transitions are composed via transition transformers.
  Internally, Isar commands are put together from an empty transition
  extended by name and source position (and optional source text).  It
  is then left to the individual command parser to turn the given
  syntax body into a suitable transition transformer that adjoin
  actual operations on a theory or proof state etc.
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
  @{index_ML Toplevel.proof_to_theory: "(Proof.state -> theory) ->
  Toplevel.transition -> Toplevel.transition"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Toplevel.print} sets the print flag, which causes the
  resulting state of the transition to be echoed in interactive mode.

  \item @{ML Toplevel.no_timing} indicates that the transition should
  never show timing information, e.g.\ because it is merely a
  diagnostic command.

  \item @{ML Toplevel.keep} adjoins a diagnostic function.

  \item @{ML Toplevel.theory} adjoins a theory transformer.

  \item @{ML Toplevel.theory_to_proof} adjoins a global goal function,
  which turns a theory into a proof state.  The theory must not be
  changed here!  The generic Isar goal setup includes an argument that
  specifies how to apply the proven result to the theory, when the
  proof is finished.

  \item @{ML Toplevel.proof} adjoins a deterministic proof command,
  with a singleton result state.

  \item @{ML Toplevel.proofs} adjoins a general proof command, with
  zero or more result states (represented as a lazy list).

  \item @{ML Toplevel.proof_to_theory} adjoins a concluding proof
  command, that returns the resulting theory, after storing the
  resulting facts etc.

  \end{description}
*}


subsection {* Toplevel control *}

text {* Apart from regular toplevel transactions there are a few
  special control commands that modify the behavior the toplevel
  itself, and only make sense in interactive mode.  Under normal
  circumstances, the user encounters these only implicitly as part of
  the protocol between the Isabelle/Isar system and a user-interface
  such as ProofGeneral.

  \begin{description}

  \item \isacommand{undo} follows the three-level hierarchy of empty
  toplevel vs.\ theory vs.\ proof: undo within a proof reverts to the
  previous proof context, undo after a proof reverts to the theory
  before the initial goal statement, undo of a theory command reverts
  to the previous theory value, undo of a theory header discontinues
  the current theory development and removes it from the theory
  database (\secref{sec:theory-database}).

  \item \isacommand{kill} aborts the current level of development:
  kill in a proof context reverts to the theory before the initial
  goal statement, kill in a theory context aborts the current theory
  development, removing it from the database.

  \item \isacommand{exit} drops out of the Isar toplevel into the
  underlying {\ML} toplevel (\secref{sec:ML-toplevel}).  The Isar
  toplevel state is preserved and may be continued later.

  \item \isacommand{quit} terminates the Isabelle/Isar process without
  saving.

  \end{description}
*}


section {* ML toplevel \label{sec:ML-toplevel} *}

text {* The {\ML} toplevel provides a read-compile-eval-print loop for
  {\ML} values, types, structures, and functors.  {\ML} declarations
  operate on the global system state, which consists of the compiler
  environment plus the values of {\ML} reference variables.  There is
  no clean way to undo {\ML} declarations, except for reverting to a
  previously saved state of the whole Isabelle process.  {\ML} input
  is either read interactively from a TTY, or from a string (usually
  within a theory text), or from a source file (usually associated
  with a theory).

  Whenever the {\ML} toplevel is active, the current Isabelle theory
  context is passed as an internal reference variable.  Thus {\ML}
  code may access the theory context during compilation, it may even
  change the value of a theory being under construction --- following
  the usual linearity restrictions (cf.~\secref{sec:context-theory}).
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML context: "theory -> unit"} \\
  @{index_ML the_context: "unit -> theory"} \\
  @{index_ML "Context.>> ": "(theory -> theory) -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML context}~@{text thy} sets the {\ML} theory context to
  @{text thy}.  This is usually performed automatically by the system,
  when dropping out of the interactive Isar toplevel into {\ML}, or
  when Isar invokes {\ML} to process code from a string or a file.

  \item @{ML "the_context ()"} refers to the theory context of the
  {\ML} toplevel --- at compile time!  {\ML} code needs to take care
  to refer to @{ML "the_context ()"} correctly, recall that evaluation
  of a function body is delayed until actual runtime.  Moreover,
  persistent {\ML} toplevel bindings to an unfinished theory should be
  avoided: code should either project out the desired information
  immediately, or produce an explicit @{ML_type theory_ref} (cf.\
  \secref{sec:context-theory}).

  \item @{ML "Context.>>"}~@{text f} applies theory transformation
  @{text f} to the current theory of the {\ML} toplevel.  In order to
  work as expected, the theory should be still under construction, and
  the Isar language element that invoked the {\ML} compiler in the
  first place shoule be ready to accept the changed theory value
  (e.g.\ \isakeyword{ML-setup}, but not plain \isakeyword{ML}).
  Otherwise the theory may get destroyed!

  \end{description}

  It is very important to note that the above functions are really
  restricted to the compile time, even though the {\ML} compiler is
  invoked at runtime!  The majority of {\ML} code uses explicit
  functional arguments of a theory or proof context, as required.
  Thus it may get run in an arbitrary context later on.

  \bigskip

  \begin{mldecls}
  @{index_ML Isar.main: "unit -> unit"} \\
  @{index_ML Isar.loop: "unit -> unit"} \\
  @{index_ML Isar.state: "unit -> Toplevel.state"} \\
  @{index_ML Isar.exn: "unit -> (exn * string) option"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML "Isar.main ()"} invokes the Isar toplevel from {\ML},
  initializing the state to empty toplevel state.

  \item @{ML "Isar.loop ()"} continues the Isar toplevel with the
  current state, after dropping out of the Isar toplevel loop.

  \item @{ML "Isar.state ()"} and @{ML "Isar.exn ()"} get current
  toplevel state and optional error condition, respectively.  This
  only works after dropping out of the Isar toplevel loop.

  \end{description}
*}


section {* Theory database *}

text {* The theory database maintains a collection of theories,
  together with some administrative information about the original
  sources, which are held in an external store (i.e.\ a collection of
  directories within the regular file system of the underlying
  platform).

  The theory database is organized as a directed acyclic graph, with
  entries referenced by theory name.  Although some external
  interfaces allow to include a directory specification, this is only
  a hint to the underlying theory loader mechanism: the internal
  theory name space is flat.

  Theory @{text A} is associated with the main theory file @{text
  A}\verb,.thy,, which needs to be accessible through the theory
  loader path.  A number of optional {\ML} source files may be
  associated with each theory, by declaring these dependencies in the
  theory header as @{text \<USES>}, and loading them consecutively
  within the theory context.  The system keeps track of incoming {\ML}
  sources and associates them with the current theory.  The special
  theory {\ML} file @{text A}\verb,.ML, is loaded after a theory has
  been concluded, in order to support legacy proof {\ML} proof
  scripts.

  The basic internal actions of the theory database are @{text
  "update"}\indexbold{@{text "update"} theory}, @{text
  "outdate"}\indexbold{@{text "outdate"} theory}, and @{text
  "remove"}\indexbold{@{text "remove"} theory}:

  \begin{itemize}

  \item @{text "update A"} introduces a link of @{text "A"} with a
  @{text "theory"} value of the same name; it asserts that the theory
  sources are consistent with that value.

  \item @{text "outdate A"} invalidates the link of a theory database
  entry to its sources, but retains the present theory value.

  \item @{text "remove A"} removes entry @{text "A"} from the theory
  database.
  
  \end{itemize}

  These actions are propagated to sub- or super-graphs of a theory
  entry in the usual way, in order to preserve global consistency of
  the state of all loaded theories with the sources of the external
  store.  This implies causal dependencies of certain actions: @{text
  "update"} or @{text "outdate"} of an entry will @{text "outdate"}
  all descendants; @{text "remove"} will @{text "remove"} all
  descendants.

  \medskip There are separate user-level interfaces to operate on the
  theory database directly or indirectly.  The primitive actions then
  just happen automatically while working with the system.  In
  particular, processing a theory header @{text "\<THEORY> A
  \<IMPORTS> B\<^sub>1 \<dots> B\<^sub>n \<BEGIN>"} ensure that the
  sub-graph of the collective imports @{text "B\<^sub>1 \<dots> B\<^sub>n"}
  is up-to-date.  Earlier theories are reloaded as required, with
  @{text update} actions proceeding in topological order according to
  theory dependencies.  There may be also a wave of implied @{text
  outdate} actions for derived theory nodes until a stable situation
  is achieved eventually.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML theory: "string -> theory"} \\
  @{index_ML use_thy: "string -> unit"} \\
  @{index_ML update_thy: "string -> unit"} \\
  @{index_ML use_thy_only: "string -> unit"} \\
  @{index_ML update_thy_only: "string -> unit"} \\
  @{index_ML touch_thy: "string -> unit"} \\
  @{index_ML remove_thy: "string -> unit"} \\[1ex]
  @{index_ML ThyInfo.begin_theory}@{verbatim ": ... -> bool -> theory"} \\
  @{index_ML ThyInfo.end_theory: "theory -> theory"} \\
  @{index_ML ThyInfo.register_theory: "theory -> unit"} \\[1ex]
  @{verbatim "datatype action = Update | Outdate | Remove"} \\
  @{index_ML ThyInfo.add_hook: "(ThyInfo.action -> string -> unit) -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML theory}~@{text A} retrieves the theory value presently
  associated with @{text A}.  The result is not necessarily
  up-to-date!

  \item @{ML use_thy}~@{text A} loads theory @{text A} if it is absent
  or out-of-date.  It ensures that all parent theories are available
  as well, but does not reload them if older versions are already
  present.

  \item @{ML update_thy} is similar to @{ML use_thy}, but ensures that
  the @{text A} and all of its ancestors are fully up-to-date.

  \item @{ML use_thy_only}~@{text A} is like @{ML use_thy}~@{text A},
  but refrains from loading the attached @{text A}\verb,.ML, file.
  This is occasionally useful in replaying legacy {\ML} proof scripts
  by hand.
  
  \item @{ML update_thy_only} is analogous to @{ML use_thy_only}, but
  proceeds like @{ML update_thy} for ancestors.

  \item @{ML touch_thy}~@{text A} performs @{text outdate} action on
  theory @{text A} and all of its descendants.

  \item @{ML remove_thy}~@{text A} removes @{text A} and all of its
  descendants from the theory database.

  \item @{ML ThyInfo.begin_theory} is the basic operation behind a
  @{text \<THEORY>} header declaration.  The boolean argument
  indicates the strictness of treating ancestors: for @{ML true} (as
  in interactive mode) like @{ML update_thy}, and for @{ML false} (as
  in batch mode) like @{ML use_thy}.  This is {\ML} functions is
  normally not invoked directly.

  \item @{ML ThyInfo.end_theory} concludes the loading of a theory
  proper; an attached theory {\ML} file may be still loaded later on.
  This is {\ML} functions is normally not invoked directly.

  \item @{ML ThyInfo.register_theory}~{text thy} registers an existing
  theory value with the theory loader database.  There is no
  management of associated sources; this is mainly for bootstrapping.

  \item @{ML "ThyInfo.add_hook"}~@{text f} registers function @{text
  f} as a hook for theory database actions.  The function will be
  invoked with the action and theory name being involved; thus derived
  actions may be performed in associated system components, e.g.\
  maintaining the state of an editor for theory sources.

  The kind and order of actions occurring in practice depends both on
  user interactions and the internal process of resolving theory
  imports.  Hooks should not rely on a particular policy here!  Any
  exceptions raised by the hook are ignored by the theory database.

  \end{description}
*}


(* FIXME section {* Sessions and document preparation *} *)

end
