(*:maxLineLen=78:*)

theory Integration
imports Base
begin

chapter \<open>System integration\<close>

section \<open>Isar toplevel \label{sec:isar-toplevel}\<close>

text \<open>
  The Isar \<^emph>\<open>toplevel state\<close> represents the outermost configuration that is
  transformed by a sequence of transitions (commands) within a theory body.
  This is a pure value with pure functions acting on it in a timeless and
  stateless manner. Historically, the sequence of transitions was wrapped up
  as sequential command loop, such that commands are applied one-by-one. In
  contemporary Isabelle/Isar, processing toplevel commands usually works in
  parallel in multi-threaded Isabelle/ML @{cite "Wenzel:2009" and
  "Wenzel:2013:ITP"}.
\<close>


subsection \<open>Toplevel state\<close>

text \<open>
  The toplevel state is a disjoint sum of empty \<open>toplevel\<close>, or \<open>theory\<close>, or
  \<open>proof\<close>. The initial toplevel is empty; a theory is commenced by a @{command
  theory} header; within a theory we may use theory commands such as @{command
  definition}, or state a @{command theorem} to be proven. A proof state
  accepts a rich collection of Isar proof commands for structured proof
  composition, or unstructured proof scripts. When the proof is concluded we
  get back to the (local) theory, which is then updated by defining the
  resulting fact. Further theory declarations or theorem statements with
  proofs may follow, until we eventually conclude the theory development by
  issuing @{command end} to get back to the empty toplevel.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Toplevel.state} \\
  @{define_ML_exception Toplevel.UNDEF} \\
  @{define_ML Toplevel.is_toplevel: "Toplevel.state -> bool"} \\
  @{define_ML Toplevel.theory_of: "Toplevel.state -> theory"} \\
  @{define_ML Toplevel.proof_of: "Toplevel.state -> Proof.state"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Toplevel.state\<close> represents Isar toplevel states, which are
  normally manipulated through the concept of toplevel transitions only
  (\secref{sec:toplevel-transition}).

  \<^descr> \<^ML>\<open>Toplevel.UNDEF\<close> is raised for undefined toplevel operations. Many
  operations work only partially for certain cases, since \<^ML_type>\<open>Toplevel.state\<close> is a sum type.

  \<^descr> \<^ML>\<open>Toplevel.is_toplevel\<close>~\<open>state\<close> checks for an empty toplevel state.

  \<^descr> \<^ML>\<open>Toplevel.theory_of\<close>~\<open>state\<close> selects the background theory of \<open>state\<close>,
  it raises \<^ML>\<open>Toplevel.UNDEF\<close> for an empty toplevel state.

  \<^descr> \<^ML>\<open>Toplevel.proof_of\<close>~\<open>state\<close> selects the Isar proof state if available,
  otherwise it raises an error.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "Isar.state"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^descr> \<open>@{Isar.state}\<close> refers to Isar toplevel state at that point --- as
  abstract value.

  This only works for diagnostic ML commands, such as @{command ML_val} or
  @{command ML_command}.
\<close>


subsection \<open>Toplevel transitions \label{sec:toplevel-transition}\<close>

text \<open>
  An Isar toplevel transition consists of a partial function on the toplevel
  state, with additional information for diagnostics and error reporting:
  there are fields for command name, source position, and other meta-data.

  The operational part is represented as the sequential union of a list of
  partial functions, which are tried in turn until the first one succeeds.
  This acts like an outer case-expression for various alternative state
  transitions. For example, \<^theory_text>\<open>qed\<close> works differently for a local proofs vs.\
  the global ending of an outermost proof.

  Transitions are composed via transition transformers. Internally, Isar
  commands are put together from an empty transition extended by name and
  source position. It is then left to the individual command parser to turn
  the given concrete syntax into a suitable transition transformer that
  adjoins actual operations on a theory or proof state.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Toplevel.keep: "(Toplevel.state -> unit) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{define_ML Toplevel.theory: "(theory -> theory) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{define_ML Toplevel.theory_to_proof: "(theory -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{define_ML Toplevel.proof: "(Proof.state -> Proof.state) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{define_ML Toplevel.proofs: "(Proof.state -> Proof.state Seq.result Seq.seq) ->
  Toplevel.transition -> Toplevel.transition"} \\
  @{define_ML Toplevel.end_proof: "(bool -> Proof.state -> Proof.context) ->
  Toplevel.transition -> Toplevel.transition"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Toplevel.keep\<close>~\<open>tr\<close> adjoins a diagnostic function.

  \<^descr> \<^ML>\<open>Toplevel.theory\<close>~\<open>tr\<close> adjoins a theory transformer.

  \<^descr> \<^ML>\<open>Toplevel.theory_to_proof\<close>~\<open>tr\<close> adjoins a global goal function, which
  turns a theory into a proof state. The theory may be changed before entering
  the proof; the generic Isar goal setup includes an \<^verbatim>\<open>after_qed\<close> argument
  that specifies how to apply the proven result to the enclosing context, when
  the proof is finished.

  \<^descr> \<^ML>\<open>Toplevel.proof\<close>~\<open>tr\<close> adjoins a deterministic proof command, with a
  singleton result.

  \<^descr> \<^ML>\<open>Toplevel.proofs\<close>~\<open>tr\<close> adjoins a general proof command, with zero or
  more result states (represented as a lazy list).

  \<^descr> \<^ML>\<open>Toplevel.end_proof\<close>~\<open>tr\<close> adjoins a concluding proof command, that
  returns the resulting theory, after applying the resulting facts to the
  target context.
\<close>

text %mlex \<open>
  The file \<^file>\<open>~~/src/HOL/Examples/Commands.thy\<close> shows some example Isar command
  definitions, with the all-important theory header declarations for outer
  syntax keywords.
\<close>


section \<open>Theory loader database\<close>

text \<open>
  In batch mode and within dumped logic images, the theory database maintains
  a collection of theories as a directed acyclic graph. A theory may refer to
  other theories as @{keyword "imports"}, or to auxiliary files via special
  \<^emph>\<open>load commands\<close> (e.g.\ @{command ML_file}). For each theory, the base
  directory of its own theory file is called \<^emph>\<open>master directory\<close>: this is used
  as the relative location to refer to other files from that theory.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML use_thy: "string -> unit"} \\
  @{define_ML Thy_Info.get_theory: "string -> theory"} \\
  @{define_ML Thy_Info.remove_thy: "string -> unit"} \\
  @{define_ML Thy_Info.register_thy: "theory -> unit"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>use_thy\<close>~\<open>A\<close> ensures that theory \<open>A\<close> is fully up-to-date wrt.\ the
  external file store; outdated ancestors are reloaded on demand.

  \<^descr> \<^ML>\<open>Thy_Info.get_theory\<close>~\<open>A\<close> retrieves the theory value presently
  associated with name \<open>A\<close>. Note that the result might be outdated wrt.\ the
  file-system content.

  \<^descr> \<^ML>\<open>Thy_Info.remove_thy\<close>~\<open>A\<close> deletes theory \<open>A\<close> and all descendants from
  the theory database.

  \<^descr> \<^ML>\<open>Thy_Info.register_thy\<close>~\<open>text thy\<close> registers an existing theory value
  with the theory loader database and updates source version information
  according to the file store.
\<close>

end
