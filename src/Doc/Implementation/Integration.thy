(*:wrap=hard:maxLineLen=78:*)

theory Integration
imports Base
begin

chapter \<open>System integration\<close>

section \<open>Isar toplevel \label{sec:isar-toplevel}\<close>

text \<open>
  The Isar \emph{toplevel state} represents the outermost configuration that
  is transformed by a sequence of transitions (commands) within a theory body.
  This is a pure value with pure functions acting on it in a timeless and
  stateless manner. Historically, the sequence of transitions was wrapped up
  as sequential command loop, such that commands are applied one-by-one. In
  contemporary Isabelle/Isar, processing toplevel commands usually works in
  parallel in multi-threaded Isabelle/ML @{cite "Wenzel:2009" and
  "Wenzel:2013:ITP"}.
\<close>


subsection \<open>Toplevel state\<close>

text \<open>
  The toplevel state is a disjoint sum of empty @{text toplevel}, or @{text
  theory}, or @{text proof}. The initial toplevel is empty; a theory is
  commenced by a @{command theory} header; within a theory we may use theory
  commands such as @{command definition}, or state a @{command theorem} to be
  proven. A proof state accepts a rich collection of Isar proof commands for
  structured proof composition, or unstructured proof scripts. When the proof
  is concluded we get back to the (local) theory, which is then updated by
  defining the resulting fact. Further theory declarations or theorem
  statements with proofs may follow, until we eventually conclude the theory
  development by issuing @{command end} to get back to the empty toplevel.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML_type Toplevel.state} \\
  @{index_ML_exception Toplevel.UNDEF} \\
  @{index_ML Toplevel.is_toplevel: "Toplevel.state -> bool"} \\
  @{index_ML Toplevel.theory_of: "Toplevel.state -> theory"} \\
  @{index_ML Toplevel.proof_of: "Toplevel.state -> Proof.state"} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type Toplevel.state} represents Isar toplevel
  states, which are normally manipulated through the concept of
  toplevel transitions only (\secref{sec:toplevel-transition}).

  \item @{ML Toplevel.UNDEF} is raised for undefined toplevel
  operations.  Many operations work only partially for certain cases,
  since @{ML_type Toplevel.state} is a sum type.

  \item @{ML Toplevel.is_toplevel}~@{text "state"} checks for an empty
  toplevel state.

  \item @{ML Toplevel.theory_of}~@{text "state"} selects the
  background theory of @{text "state"}, it raises @{ML Toplevel.UNDEF}
  for an empty toplevel state.

  \item @{ML Toplevel.proof_of}~@{text "state"} selects the Isar proof
  state if available, otherwise it raises @{ML Toplevel.UNDEF}.

  \end{description}
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "Isar.state"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  \begin{description}

  \item @{text "@{Isar.state}"} refers to Isar toplevel state at that
  point --- as abstract value.

  This only works for diagnostic ML commands, such as @{command
  ML_val} or @{command ML_command}.

  \end{description}
\<close>


subsection \<open>Toplevel transitions \label{sec:toplevel-transition}\<close>

text \<open>
  An Isar toplevel transition consists of a partial function on the toplevel
  state, with additional information for diagnostics and error reporting:
  there are fields for command name, source position, and other meta-data.

  The operational part is represented as the sequential union of a
  list of partial functions, which are tried in turn until the first
  one succeeds.  This acts like an outer case-expression for various
  alternative state transitions.  For example, \isakeyword{qed} works
  differently for a local proofs vs.\ the global ending of an outermost
  proof.

  Transitions are composed via transition transformers. Internally, Isar
  commands are put together from an empty transition extended by name and
  source position. It is then left to the individual command parser to turn
  the given concrete syntax into a suitable transition transformer that
  adjoins actual operations on a theory or proof state.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML Toplevel.keep: "(Toplevel.state -> unit) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.theory: "(theory -> theory) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.theory_to_proof: "(theory -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.proof: "(Proof.state -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.proofs: "(Proof.state -> Proof.state Seq.result Seq.seq) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{index_ML Toplevel.end_proof: "(bool -> Proof.state -> Proof.context) ->
  Toplevel.transition -> Toplevel.transition"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Toplevel.keep}~@{text "tr"} adjoins a diagnostic
  function.

  \item @{ML Toplevel.theory}~@{text "tr"} adjoins a theory
  transformer.

  \item @{ML Toplevel.theory_to_proof}~@{text "tr"} adjoins a global
  goal function, which turns a theory into a proof state.  The theory
  may be changed before entering the proof; the generic Isar goal
  setup includes an @{verbatim after_qed} argument that specifies how to
  apply the proven result to the enclosing context, when the proof
  is finished.

  \item @{ML Toplevel.proof}~@{text "tr"} adjoins a deterministic
  proof command, with a singleton result.

  \item @{ML Toplevel.proofs}~@{text "tr"} adjoins a general proof
  command, with zero or more result states (represented as a lazy
  list).

  \item @{ML Toplevel.end_proof}~@{text "tr"} adjoins a concluding
  proof command, that returns the resulting theory, after applying the
  resulting facts to the target context.

  \end{description}
\<close>

text %mlex \<open>The file @{"file" "~~/src/HOL/ex/Commands.thy"} shows some example
Isar command definitions, with the all-important theory header declarations
for outer syntax keywords.\<close>


section \<open>Theory loader database\<close>

text \<open>
  In batch mode and within dumped logic images, the theory database maintains
  a collection of theories as a directed acyclic graph. A theory may refer to
  other theories as @{keyword "imports"}, or to auxiliary files via special
  \emph{load commands} (e.g.\ @{command ML_file}). For each theory, the base
  directory of its own theory file is called \emph{master directory}: this is
  used as the relative location to refer to other files from that theory.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{index_ML use_thy: "string -> unit"} \\
  @{index_ML use_thys: "string list -> unit"} \\[0.5ex]
  @{index_ML Thy_Info.get_theory: "string -> theory"} \\
  @{index_ML Thy_Info.remove_thy: "string -> unit"} \\
  @{index_ML Thy_Info.register_thy: "theory -> unit"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML use_thy}~@{text A} ensures that theory @{text A} is fully
  up-to-date wrt.\ the external file store; outdated ancestors are reloaded on
  demand.

  \item @{ML use_thys} is similar to @{ML use_thy}, but handles several
  theories simultaneously. Thus it acts like processing the import header of a
  theory, without performing the merge of the result. By loading a whole
  sub-graph of theories, the intrinsic parallelism can be exploited by the
  system to speedup loading.

  This variant is used by default in @{tool build} @{cite "isabelle-sys"}.

  \item @{ML Thy_Info.get_theory}~@{text A} retrieves the theory value
  presently associated with name @{text A}. Note that the result might be
  outdated wrt.\ the file-system content.

  \item @{ML Thy_Info.remove_thy}~@{text A} deletes theory @{text A} and all
  descendants from the theory database.

  \item @{ML Thy_Info.register_thy}~@{text "text thy"} registers an existing
  theory value with the theory loader database and updates source version
  information according to the file store.

  \end{description}
\<close>

end
