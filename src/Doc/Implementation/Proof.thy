(*:maxLineLen=78:*)

theory Proof
imports Base
begin

chapter \<open>Structured proofs\<close>

section \<open>Variables \label{sec:variables}\<close>

text \<open>
  Any variable that is not explicitly bound by \<open>\<lambda>\<close>-abstraction is considered
  as ``free''. Logically, free variables act like outermost universal
  quantification at the sequent level: \<open>A\<^sub>1(x), \<dots>, A\<^sub>n(x) \<turnstile> B(x)\<close> means that
  the result holds \<^emph>\<open>for all\<close> values of \<open>x\<close>. Free variables for terms (not
  types) can be fully internalized into the logic: \<open>\<turnstile> B(x)\<close> and \<open>\<turnstile> \<And>x. B(x)\<close>
  are interchangeable, provided that \<open>x\<close> does not occur elsewhere in the
  context. Inspecting \<open>\<turnstile> \<And>x. B(x)\<close> more closely, we see that inside the
  quantifier, \<open>x\<close> is essentially ``arbitrary, but fixed'', while from outside
  it appears as a place-holder for instantiation (thanks to \<open>\<And>\<close> elimination).

  The Pure logic represents the idea of variables being either inside or
  outside the current scope by providing separate syntactic categories for
  \<^emph>\<open>fixed variables\<close> (e.g.\ \<open>x\<close>) vs.\ \<^emph>\<open>schematic variables\<close> (e.g.\ \<open>?x\<close>).
  Incidently, a universal result \<open>\<turnstile> \<And>x. B(x)\<close> has the HHF normal form \<open>\<turnstile>
  B(?x)\<close>, which represents its generality without requiring an explicit
  quantifier. The same principle works for type variables: \<open>\<turnstile> B(?\<alpha>)\<close>
  represents the idea of ``\<open>\<turnstile> \<forall>\<alpha>. B(\<alpha>)\<close>'' without demanding a truly
  polymorphic framework.

  \<^medskip>
  Additional care is required to treat type variables in a way that
  facilitates type-inference. In principle, term variables depend on type
  variables, which means that type variables would have to be declared first.
  For example, a raw type-theoretic framework would demand the context to be
  constructed in stages as follows: \<open>\<Gamma> = \<alpha>: type, x: \<alpha>, a: A(x\<^sub>\<alpha>)\<close>.

  We allow a slightly less formalistic mode of operation: term variables \<open>x\<close>
  are fixed without specifying a type yet (essentially \<^emph>\<open>all\<close> potential
  occurrences of some instance \<open>x\<^sub>\<tau>\<close> are fixed); the first occurrence of \<open>x\<close>
  within a specific term assigns its most general type, which is then
  maintained consistently in the context. The above example becomes \<open>\<Gamma> = x:
  term, \<alpha>: type, A(x\<^sub>\<alpha>)\<close>, where type \<open>\<alpha>\<close> is fixed \<^emph>\<open>after\<close> term \<open>x\<close>, and the
  constraint \<open>x :: \<alpha>\<close> is an implicit consequence of the occurrence of \<open>x\<^sub>\<alpha>\<close> in
  the subsequent proposition.

  This twist of dependencies is also accommodated by the reverse operation of
  exporting results from a context: a type variable \<open>\<alpha>\<close> is considered fixed as
  long as it occurs in some fixed term variable of the context. For example,
  exporting \<open>x: term, \<alpha>: type \<turnstile> x\<^sub>\<alpha> \<equiv> x\<^sub>\<alpha>\<close> produces in the first step \<open>x: term
  \<turnstile> x\<^sub>\<alpha> \<equiv> x\<^sub>\<alpha>\<close> for fixed \<open>\<alpha>\<close>, and only in the second step \<open>\<turnstile> ?x\<^sub>?\<^sub>\<alpha> \<equiv> ?x\<^sub>?\<^sub>\<alpha>\<close>
  for schematic \<open>?x\<close> and \<open>?\<alpha>\<close>. The following Isar source text illustrates this
  scenario.
\<close>

notepad
begin
  {
    fix x  \<comment> \<open>all potential occurrences of some \<open>x::\<tau>\<close> are fixed\<close>
    {
      have "x::'a \<equiv> x"  \<comment> \<open>implicit type assignment by concrete occurrence\<close>
        by (rule reflexive)
    }
    thm this  \<comment> \<open>result still with fixed type \<open>'a\<close>\<close>
  }
  thm this  \<comment> \<open>fully general result for arbitrary \<open>?x::?'a\<close>\<close>
end

text \<open>
  The Isabelle/Isar proof context manages the details of term vs.\ type
  variables, with high-level principles for moving the frontier between fixed
  and schematic variables.

  The \<open>add_fixes\<close> operation explicitly declares fixed variables; the
  \<open>declare_term\<close> operation absorbs a term into a context by fixing new type
  variables and adding syntactic constraints.

  The \<open>export\<close> operation is able to perform the main work of generalizing term
  and type variables as sketched above, assuming that fixing variables and
  terms have been declared properly.

  There \<open>import\<close> operation makes a generalized fact a genuine part of the
  context, by inventing fixed variables for the schematic ones. The effect can
  be reversed by using \<open>export\<close> later, potentially with an extended context;
  the result is equivalent to the original modulo renaming of schematic
  variables.

  The \<open>focus\<close> operation provides a variant of \<open>import\<close> for nested propositions
  (with explicit quantification): \<open>\<And>x\<^sub>1 \<dots> x\<^sub>n. B(x\<^sub>1, \<dots>, x\<^sub>n)\<close> is decomposed
  by inventing fixed variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> for the body.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML Variable.add_fixes: "
  string list -> Proof.context -> string list * Proof.context"} \\
  @{define_ML Variable.variant_fixes: "
  string list -> Proof.context -> string list * Proof.context"} \\
  @{define_ML Variable.declare_term: "term -> Proof.context -> Proof.context"} \\
  @{define_ML Variable.declare_constraints: "term -> Proof.context -> Proof.context"} \\
  @{define_ML Variable.export: "Proof.context -> Proof.context -> thm list -> thm list"} \\
  @{define_ML Variable.polymorphic: "Proof.context -> term list -> term list"} \\
  @{define_ML Variable.import: "bool -> thm list -> Proof.context ->
  ((ctyp Term_Subst.TVars.table * cterm Term_Subst.Vars.table) * thm list)
    * Proof.context"} \\
  @{define_ML Variable.focus: "binding list option -> term -> Proof.context ->
  ((string * (string * typ)) list * term) * Proof.context"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>Variable.add_fixes\<close>~\<open>xs ctxt\<close> fixes term variables \<open>xs\<close>, returning
  the resulting internal names. By default, the internal representation
  coincides with the external one, which also means that the given variables
  must not be fixed already. There is a different policy within a local proof
  body: the given names are just hints for newly invented Skolem variables.

  \<^descr> \<^ML>\<open>Variable.variant_fixes\<close> is similar to \<^ML>\<open>Variable.add_fixes\<close>, but
  always produces fresh variants of the given names.

  \<^descr> \<^ML>\<open>Variable.declare_term\<close>~\<open>t ctxt\<close> declares term \<open>t\<close> to belong to the
  context. This automatically fixes new type variables, but not term
  variables. Syntactic constraints for type and term variables are declared
  uniformly, though.

  \<^descr> \<^ML>\<open>Variable.declare_constraints\<close>~\<open>t ctxt\<close> declares syntactic constraints
  from term \<open>t\<close>, without making it part of the context yet.

  \<^descr> \<^ML>\<open>Variable.export\<close>~\<open>inner outer thms\<close> generalizes fixed type and term
  variables in \<open>thms\<close> according to the difference of the \<open>inner\<close> and \<open>outer\<close>
  context, following the principles sketched above.

  \<^descr> \<^ML>\<open>Variable.polymorphic\<close>~\<open>ctxt ts\<close> generalizes type variables in \<open>ts\<close> as
  far as possible, even those occurring in fixed term variables. The default
  policy of type-inference is to fix newly introduced type variables, which is
  essentially reversed with \<^ML>\<open>Variable.polymorphic\<close>: here the given terms
  are detached from the context as far as possible.

  \<^descr> \<^ML>\<open>Variable.import\<close>~\<open>open thms ctxt\<close> invents fixed type and term
  variables for the schematic ones occurring in \<open>thms\<close>. The \<open>open\<close> flag
  indicates whether the fixed names should be accessible to the user,
  otherwise newly introduced names are marked as ``internal''
  (\secref{sec:names}).

  \<^descr> \<^ML>\<open>Variable.focus\<close>~\<open>bindings B\<close> decomposes the outermost \<open>\<And>\<close> prefix of
  proposition \<open>B\<close>, using the given name bindings.
\<close>

text %mlex \<open>
  The following example shows how to work with fixed term and type parameters
  and with type-inference.
\<close>

ML_val \<open>
  (*static compile-time context -- for testing only*)
  val ctxt0 = \<^context>;

  (*locally fixed parameters -- no type assignment yet*)
  val ([x, y], ctxt1) = ctxt0 |> Variable.add_fixes ["x", "y"];

  (*t1: most general fixed type; t1': most general arbitrary type*)
  val t1 = Syntax.read_term ctxt1 "x";
  val t1' = singleton (Variable.polymorphic ctxt1) t1;

  (*term u enforces specific type assignment*)
  val u = Syntax.read_term ctxt1 "(x::nat) \<equiv> y";

  (*official declaration of u -- propagates constraints etc.*)
  val ctxt2 = ctxt1 |> Variable.declare_term u;
  val t2 = Syntax.read_term ctxt2 "x";  (*x::nat is enforced*)
\<close>

text \<open>
  In the above example, the starting context is derived from the toplevel
  theory, which means that fixed variables are internalized literally: \<open>x\<close> is
  mapped again to \<open>x\<close>, and attempting to fix it again in the subsequent
  context is an error. Alternatively, fixed parameters can be renamed
  explicitly as follows:
\<close>

ML_val \<open>
  val ctxt0 = \<^context>;
  val ([x1, x2, x3], ctxt1) =
    ctxt0 |> Variable.variant_fixes ["x", "x", "x"];
\<close>

text \<open>
  The following ML code can now work with the invented names of \<open>x1\<close>, \<open>x2\<close>,
  \<open>x3\<close>, without depending on the details on the system policy for introducing
  these variants. Recall that within a proof body the system always invents
  fresh ``Skolem constants'', e.g.\ as follows:
\<close>

notepad
begin
  ML_prf %"ML"
   \<open>val ctxt0 = \<^context>;

    val ([x1], ctxt1) = ctxt0 |> Variable.add_fixes ["x"];
    val ([x2], ctxt2) = ctxt1 |> Variable.add_fixes ["x"];
    val ([x3], ctxt3) = ctxt2 |> Variable.add_fixes ["x"];

    val ([y1, y2], ctxt4) =
      ctxt3 |> Variable.variant_fixes ["y", "y"];\<close>
end

text \<open>
  In this situation \<^ML>\<open>Variable.add_fixes\<close> and \<^ML>\<open>Variable.variant_fixes\<close>
  are very similar, but identical name proposals given in a row are only
  accepted by the second version.
\<close>


section \<open>Assumptions \label{sec:assumptions}\<close>

text \<open>
  An \<^emph>\<open>assumption\<close> is a proposition that it is postulated in the current
  context. Local conclusions may use assumptions as additional facts, but this
  imposes implicit hypotheses that weaken the overall statement.

  Assumptions are restricted to fixed non-schematic statements, i.e.\ all
  generality needs to be expressed by explicit quantifiers. Nevertheless, the
  result will be in HHF normal form with outermost quantifiers stripped. For
  example, by assuming \<open>\<And>x :: \<alpha>. P x\<close> we get \<open>\<And>x :: \<alpha>. P x \<turnstile> P ?x\<close> for
  schematic \<open>?x\<close> of fixed type \<open>\<alpha>\<close>. Local derivations accumulate more and more
  explicit references to hypotheses: \<open>A\<^sub>1, \<dots>, A\<^sub>n \<turnstile> B\<close> where \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>
  needs to be covered by the assumptions of the current context.

  \<^medskip>
  The \<open>add_assms\<close> operation augments the context by local assumptions, which
  are parameterized by an arbitrary \<open>export\<close> rule (see below).

  The \<open>export\<close> operation moves facts from a (larger) inner context into a
  (smaller) outer context, by discharging the difference of the assumptions as
  specified by the associated export rules. Note that the discharged portion
  is determined by the difference of contexts, not the facts being exported!
  There is a separate flag to indicate a goal context, where the result is
  meant to refine an enclosing sub-goal of a structured proof state.

  \<^medskip>
  The most basic export rule discharges assumptions directly by means of the
  \<open>\<Longrightarrow>\<close> introduction rule:
  \[
  \infer[(\<open>\<Longrightarrow>\<hyphen>intro\<close>)]{\<open>\<Gamma> - A \<turnstile> A \<Longrightarrow> B\<close>}{\<open>\<Gamma> \<turnstile> B\<close>}
  \]

  The variant for goal refinements marks the newly introduced premises, which
  causes the canonical Isar goal refinement scheme to enforce unification with
  local premises within the goal:
  \[
  \infer[(\<open>#\<Longrightarrow>\<hyphen>intro\<close>)]{\<open>\<Gamma> - A \<turnstile> #A \<Longrightarrow> B\<close>}{\<open>\<Gamma> \<turnstile> B\<close>}
  \]

  \<^medskip>
  Alternative versions of assumptions may perform arbitrary transformations on
  export, as long as the corresponding portion of hypotheses is removed from
  the given facts. For example, a local definition works by fixing \<open>x\<close> and
  assuming \<open>x \<equiv> t\<close>, with the following export rule to reverse the effect:
  \[
  \infer[(\<open>\<equiv>\<hyphen>expand\<close>)]{\<open>\<Gamma> - (x \<equiv> t) \<turnstile> B t\<close>}{\<open>\<Gamma> \<turnstile> B x\<close>}
  \]
  This works, because the assumption \<open>x \<equiv> t\<close> was introduced in a context with
  \<open>x\<close> being fresh, so \<open>x\<close> does not occur in \<open>\<Gamma>\<close> here.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Assumption.export} \\
  @{define_ML Assumption.assume: "Proof.context -> cterm -> thm"} \\
  @{define_ML Assumption.add_assms:
    "Assumption.export ->
  cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{define_ML Assumption.add_assumes: "
  cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{define_ML Assumption.export: "bool -> Proof.context -> Proof.context -> thm -> thm"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Assumption.export\<close> represents arbitrary export rules, which
  is any function of type \<^ML_type>\<open>bool -> cterm list -> thm -> thm\<close>, where
  the \<^ML_type>\<open>bool\<close> indicates goal mode, and the \<^ML_type>\<open>cterm list\<close>
  the collection of assumptions to be discharged simultaneously.

  \<^descr> \<^ML>\<open>Assumption.assume\<close>~\<open>ctxt A\<close> turns proposition \<open>A\<close> into a primitive
  assumption \<open>A \<turnstile> A'\<close>, where the conclusion \<open>A'\<close> is in HHF normal form.

  \<^descr> \<^ML>\<open>Assumption.add_assms\<close>~\<open>r As\<close> augments the context by assumptions \<open>As\<close>
  with export rule \<open>r\<close>. The resulting facts are hypothetical theorems as
  produced by the raw \<^ML>\<open>Assumption.assume\<close>.

  \<^descr> \<^ML>\<open>Assumption.add_assumes\<close>~\<open>As\<close> is a special case of \<^ML>\<open>Assumption.add_assms\<close> where the export rule performs \<open>\<Longrightarrow>\<hyphen>intro\<close> or
  \<open>#\<Longrightarrow>\<hyphen>intro\<close>, depending on goal mode.

  \<^descr> \<^ML>\<open>Assumption.export\<close>~\<open>is_goal inner outer thm\<close> exports result \<open>thm\<close>
  from the the \<open>inner\<close> context back into the \<open>outer\<close> one; \<open>is_goal = true\<close>
  means this is a goal context. The result is in HHF normal form. Note that
  \<^ML>\<open>Proof_Context.export\<close> combines \<^ML>\<open>Variable.export\<close> and \<^ML>\<open>Assumption.export\<close> in the canonical way.
\<close>

text %mlex \<open>
  The following example demonstrates how rules can be derived by building up a
  context of assumptions first, and exporting some local fact afterwards. We
  refer to \<^theory>\<open>Pure\<close> equality here for testing purposes.
\<close>

ML_val \<open>
  (*static compile-time context -- for testing only*)
  val ctxt0 = \<^context>;

  val ([eq], ctxt1) =
    ctxt0 |> Assumption.add_assumes [\<^cprop>\<open>x \<equiv> y\<close>];
  val eq' = Thm.symmetric eq;

  (*back to original context -- discharges assumption*)
  val r = Assumption.export false ctxt1 ctxt0 eq';
\<close>

text \<open>
  Note that the variables of the resulting rule are not generalized. This
  would have required to fix them properly in the context beforehand, and
  export wrt.\ variables afterwards (cf.\ \<^ML>\<open>Variable.export\<close> or the
  combined \<^ML>\<open>Proof_Context.export\<close>).
\<close>


section \<open>Structured goals and results \label{sec:struct-goals}\<close>

text \<open>
  Local results are established by monotonic reasoning from facts within a
  context. This allows common combinations of theorems, e.g.\ via \<open>\<And>/\<Longrightarrow>\<close>
  elimination, resolution rules, or equational reasoning, see
  \secref{sec:thms}. Unaccounted context manipulations should be avoided,
  notably raw \<open>\<And>/\<Longrightarrow>\<close> introduction or ad-hoc references to free variables or
  assumptions not present in the proof context.

  \<^medskip>
  The \<open>SUBPROOF\<close> combinator allows to structure a tactical proof recursively
  by decomposing a selected sub-goal: \<open>(\<And>x. A(x) \<Longrightarrow> B(x)) \<Longrightarrow> \<dots>\<close> is turned into
  \<open>B(x) \<Longrightarrow> \<dots>\<close> after fixing \<open>x\<close> and assuming \<open>A(x)\<close>. This means the tactic needs
  to solve the conclusion, but may use the premise as a local fact, for
  locally fixed variables.

  The family of \<open>FOCUS\<close> combinators is similar to \<open>SUBPROOF\<close>, but allows to
  retain schematic variables and pending subgoals in the resulting goal state.

  The \<open>prove\<close> operation provides an interface for structured backwards
  reasoning under program control, with some explicit sanity checks of the
  result. The goal context can be augmented by additional fixed variables
  (cf.\ \secref{sec:variables}) and assumptions (cf.\
  \secref{sec:assumptions}), which will be available as local facts during the
  proof and discharged into implications in the result. Type and term
  variables are generalized as usual, according to the context.

  The \<open>obtain\<close> operation produces results by eliminating existing facts by
  means of a given tactic. This acts like a dual conclusion: the proof
  demonstrates that the context may be augmented by parameters and
  assumptions, without affecting any conclusions that do not mention these
  parameters. See also @{cite "isabelle-isar-ref"} for the user-level
  @{command obtain} and @{command guess} elements. Final results, which may
  not refer to the parameters in the conclusion, need to exported explicitly
  into the original context.\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML SUBPROOF: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{define_ML Subgoal.FOCUS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{define_ML Subgoal.FOCUS_PREMS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{define_ML Subgoal.FOCUS_PARAMS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{define_ML Subgoal.focus: "Proof.context -> int -> binding list option ->
  thm -> Subgoal.focus * thm"} \\
  @{define_ML Subgoal.focus_prems: "Proof.context -> int -> binding list option ->
  thm -> Subgoal.focus * thm"} \\
  @{define_ML Subgoal.focus_params: "Proof.context -> int -> binding list option ->
  thm -> Subgoal.focus * thm"} \\
  \end{mldecls}

  \begin{mldecls}
  @{define_ML Goal.prove: "Proof.context -> string list -> term list -> term ->
  ({prems: thm list, context: Proof.context} -> tactic) -> thm"} \\
  @{define_ML Goal.prove_common: "Proof.context -> int option ->
  string list -> term list -> term list ->
  ({prems: thm list, context: Proof.context} -> tactic) -> thm list"} \\
  \end{mldecls}
  \begin{mldecls}
  @{define_ML Obtain.result: "(Proof.context -> tactic) -> thm list ->
  Proof.context -> ((string * cterm) list * thm list) * Proof.context"} \\
  \end{mldecls}

  \<^descr> \<^ML>\<open>SUBPROOF\<close>~\<open>tac ctxt i\<close> decomposes the structure of the specified
  sub-goal, producing an extended context and a reduced goal, which needs to
  be solved by the given tactic. All schematic parameters of the goal are
  imported into the context as fixed ones, which may not be instantiated in
  the sub-proof.

  \<^descr> \<^ML>\<open>Subgoal.FOCUS\<close>, \<^ML>\<open>Subgoal.FOCUS_PREMS\<close>, and \<^ML>\<open>Subgoal.FOCUS_PARAMS\<close> are similar to \<^ML>\<open>SUBPROOF\<close>, but are slightly more
  flexible: only the specified parts of the subgoal are imported into the
  context, and the body tactic may introduce new subgoals and schematic
  variables.

  \<^descr> \<^ML>\<open>Subgoal.focus\<close>, \<^ML>\<open>Subgoal.focus_prems\<close>, \<^ML>\<open>Subgoal.focus_params\<close>
  extract the focus information from a goal state in the same way as the
  corresponding tacticals above. This is occasionally useful to experiment
  without writing actual tactics yet.

  \<^descr> \<^ML>\<open>Goal.prove\<close>~\<open>ctxt xs As C tac\<close> states goal \<open>C\<close> in the context
  augmented by fixed variables \<open>xs\<close> and assumptions \<open>As\<close>, and applies tactic
  \<open>tac\<close> to solve it. The latter may depend on the local assumptions being
  presented as facts. The result is in HHF normal form.

  \<^descr> \<^ML>\<open>Goal.prove_common\<close>~\<open>ctxt fork_pri\<close> is the common form to state and
  prove a simultaneous goal statement, where \<^ML>\<open>Goal.prove\<close> is a convenient
  shorthand that is most frequently used in applications.

  The given list of simultaneous conclusions is encoded in the goal state by
  means of Pure conjunction: \<^ML>\<open>Goal.conjunction_tac\<close> will turn this into a
  collection of individual subgoals, but note that the original multi-goal
  state is usually required for advanced induction.

  It is possible to provide an optional priority for a forked proof, typically
  \<^ML>\<open>SOME ~1\<close>, while \<^ML>\<open>NONE\<close> means the proof is immediate (sequential)
  as for \<^ML>\<open>Goal.prove\<close>. Note that a forked proof does not exhibit any
  failures in the usual way via exceptions in ML, but accumulates error
  situations under the execution id of the running transaction. Thus the
  system is able to expose error messages ultimately to the end-user, even
  though the subsequent ML code misses them.

  \<^descr> \<^ML>\<open>Obtain.result\<close>~\<open>tac thms ctxt\<close> eliminates the given facts using a
  tactic, which results in additional fixed variables and assumptions in the
  context. Final results need to be exported explicitly.
\<close>

text %mlex \<open>
  The following minimal example illustrates how to access the focus
  information of a structured goal state.
\<close>

notepad
begin
  fix A B C :: "'a \<Rightarrow> bool"

  have "\<And>x. A x \<Longrightarrow> B x \<Longrightarrow> C x"
    ML_val
     \<open>val {goal, context = goal_ctxt, ...} = @{Isar.goal};
      val (focus as {params, asms, concl, ...}, goal') =
        Subgoal.focus goal_ctxt 1 (SOME [\<^binding>\<open>x\<close>]) goal;
      val [A, B] = #prems focus;
      val [(_, x)] = #params focus;\<close>
    sorry
end

text \<open>
  \<^medskip>
  The next example demonstrates forward-elimination in a local context, using
  \<^ML>\<open>Obtain.result\<close>.
\<close>

notepad
begin
  assume ex: "\<exists>x. B x"

  ML_prf %"ML"
   \<open>val ctxt0 = \<^context>;
    val (([(_, x)], [B]), ctxt1) = ctxt0
      |> Obtain.result (fn _ => eresolve_tac ctxt0 @{thms exE} 1) [@{thm ex}];\<close>
  ML_prf %"ML"
   \<open>singleton (Proof_Context.export ctxt1 ctxt0) @{thm refl};\<close>
  ML_prf %"ML"
   \<open>Proof_Context.export ctxt1 ctxt0 [Thm.reflexive x]
      handle ERROR msg => (warning msg; []);\<close>
end

end
