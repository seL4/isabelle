theory Proof
imports Base
begin

chapter {* Structured proofs *}

section {* Variables \label{sec:variables} *}

text {*
  Any variable that is not explicitly bound by @{text "\<lambda>"}-abstraction
  is considered as ``free''.  Logically, free variables act like
  outermost universal quantification at the sequent level: @{text
  "A\<^isub>1(x), \<dots>, A\<^isub>n(x) \<turnstile> B(x)"} means that the result
  holds \emph{for all} values of @{text "x"}.  Free variables for
  terms (not types) can be fully internalized into the logic: @{text
  "\<turnstile> B(x)"} and @{text "\<turnstile> \<And>x. B(x)"} are interchangeable, provided
  that @{text "x"} does not occur elsewhere in the context.
  Inspecting @{text "\<turnstile> \<And>x. B(x)"} more closely, we see that inside the
  quantifier, @{text "x"} is essentially ``arbitrary, but fixed'',
  while from outside it appears as a place-holder for instantiation
  (thanks to @{text "\<And>"} elimination).

  The Pure logic represents the idea of variables being either inside
  or outside the current scope by providing separate syntactic
  categories for \emph{fixed variables} (e.g.\ @{text "x"}) vs.\
  \emph{schematic variables} (e.g.\ @{text "?x"}).  Incidently, a
  universal result @{text "\<turnstile> \<And>x. B(x)"} has the HHF normal form @{text
  "\<turnstile> B(?x)"}, which represents its generality without requiring an
  explicit quantifier.  The same principle works for type variables:
  @{text "\<turnstile> B(?\<alpha>)"} represents the idea of ``@{text "\<turnstile> \<forall>\<alpha>. B(\<alpha>)"}''
  without demanding a truly polymorphic framework.

  \medskip Additional care is required to treat type variables in a
  way that facilitates type-inference.  In principle, term variables
  depend on type variables, which means that type variables would have
  to be declared first.  For example, a raw type-theoretic framework
  would demand the context to be constructed in stages as follows:
  @{text "\<Gamma> = \<alpha>: type, x: \<alpha>, a: A(x\<^isub>\<alpha>)"}.

  We allow a slightly less formalistic mode of operation: term
  variables @{text "x"} are fixed without specifying a type yet
  (essentially \emph{all} potential occurrences of some instance
  @{text "x\<^isub>\<tau>"} are fixed); the first occurrence of @{text "x"}
  within a specific term assigns its most general type, which is then
  maintained consistently in the context.  The above example becomes
  @{text "\<Gamma> = x: term, \<alpha>: type, A(x\<^isub>\<alpha>)"}, where type @{text
  "\<alpha>"} is fixed \emph{after} term @{text "x"}, and the constraint
  @{text "x :: \<alpha>"} is an implicit consequence of the occurrence of
  @{text "x\<^isub>\<alpha>"} in the subsequent proposition.

  This twist of dependencies is also accommodated by the reverse
  operation of exporting results from a context: a type variable
  @{text "\<alpha>"} is considered fixed as long as it occurs in some fixed
  term variable of the context.  For example, exporting @{text "x:
  term, \<alpha>: type \<turnstile> x\<^isub>\<alpha> \<equiv> x\<^isub>\<alpha>"} produces in the first step @{text "x: term
  \<turnstile> x\<^isub>\<alpha> \<equiv> x\<^isub>\<alpha>"} for fixed @{text "\<alpha>"}, and only in the second step
  @{text "\<turnstile> ?x\<^isub>?\<^isub>\<alpha> \<equiv> ?x\<^isub>?\<^isub>\<alpha>"} for schematic @{text "?x"} and @{text "?\<alpha>"}.
  The following Isar source text illustrates this scenario.
*}

notepad
begin
  {
    fix x  -- {* all potential occurrences of some @{text "x::\<tau>"} are fixed *}
    {
      have "x::'a \<equiv> x"  -- {* implicit type assigment by concrete occurrence *}
        by (rule reflexive)
    }
    thm this  -- {* result still with fixed type @{text "'a"} *}
  }
  thm this  -- {* fully general result for arbitrary @{text "?x::?'a"} *}
end

text {* The Isabelle/Isar proof context manages the details of term
  vs.\ type variables, with high-level principles for moving the
  frontier between fixed and schematic variables.

  The @{text "add_fixes"} operation explictly declares fixed
  variables; the @{text "declare_term"} operation absorbs a term into
  a context by fixing new type variables and adding syntactic
  constraints.

  The @{text "export"} operation is able to perform the main work of
  generalizing term and type variables as sketched above, assuming
  that fixing variables and terms have been declared properly.

  There @{text "import"} operation makes a generalized fact a genuine
  part of the context, by inventing fixed variables for the schematic
  ones.  The effect can be reversed by using @{text "export"} later,
  potentially with an extended context; the result is equivalent to
  the original modulo renaming of schematic variables.

  The @{text "focus"} operation provides a variant of @{text "import"}
  for nested propositions (with explicit quantification): @{text
  "\<And>x\<^isub>1 \<dots> x\<^isub>n. B(x\<^isub>1, \<dots>, x\<^isub>n)"} is
  decomposed by inventing fixed variables @{text "x\<^isub>1, \<dots>,
  x\<^isub>n"} for the body.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML Variable.add_fixes: "
  string list -> Proof.context -> string list * Proof.context"} \\
  @{index_ML Variable.variant_fixes: "
  string list -> Proof.context -> string list * Proof.context"} \\
  @{index_ML Variable.declare_term: "term -> Proof.context -> Proof.context"} \\
  @{index_ML Variable.declare_constraints: "term -> Proof.context -> Proof.context"} \\
  @{index_ML Variable.export: "Proof.context -> Proof.context -> thm list -> thm list"} \\
  @{index_ML Variable.polymorphic: "Proof.context -> term list -> term list"} \\
  @{index_ML Variable.import: "bool -> thm list -> Proof.context ->
  (((ctyp * ctyp) list * (cterm * cterm) list) * thm list) * Proof.context"} \\
  @{index_ML Variable.focus: "term -> Proof.context ->
  ((string * (string * typ)) list * term) * Proof.context"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML Variable.add_fixes}~@{text "xs ctxt"} fixes term
  variables @{text "xs"}, returning the resulting internal names.  By
  default, the internal representation coincides with the external
  one, which also means that the given variables must not be fixed
  already.  There is a different policy within a local proof body: the
  given names are just hints for newly invented Skolem variables.

  \item @{ML Variable.variant_fixes} is similar to @{ML
  Variable.add_fixes}, but always produces fresh variants of the given
  names.

  \item @{ML Variable.declare_term}~@{text "t ctxt"} declares term
  @{text "t"} to belong to the context.  This automatically fixes new
  type variables, but not term variables.  Syntactic constraints for
  type and term variables are declared uniformly, though.

  \item @{ML Variable.declare_constraints}~@{text "t ctxt"} declares
  syntactic constraints from term @{text "t"}, without making it part
  of the context yet.

  \item @{ML Variable.export}~@{text "inner outer thms"} generalizes
  fixed type and term variables in @{text "thms"} according to the
  difference of the @{text "inner"} and @{text "outer"} context,
  following the principles sketched above.

  \item @{ML Variable.polymorphic}~@{text "ctxt ts"} generalizes type
  variables in @{text "ts"} as far as possible, even those occurring
  in fixed term variables.  The default policy of type-inference is to
  fix newly introduced type variables, which is essentially reversed
  with @{ML Variable.polymorphic}: here the given terms are detached
  from the context as far as possible.

  \item @{ML Variable.import}~@{text "open thms ctxt"} invents fixed
  type and term variables for the schematic ones occurring in @{text
  "thms"}.  The @{text "open"} flag indicates whether the fixed names
  should be accessible to the user, otherwise newly introduced names
  are marked as ``internal'' (\secref{sec:names}).

  \item @{ML Variable.focus}~@{text B} decomposes the outermost @{text
  "\<And>"} prefix of proposition @{text "B"}.

  \end{description}
*}

text %mlex {* The following example shows how to work with fixed term
  and type parameters and with type-inference.  *}

ML {*
  (*static compile-time context -- for testing only*)
  val ctxt0 = @{context};

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
*}

text {* In the above example, the starting context is derived from the
  toplevel theory, which means that fixed variables are internalized
  literally: @{text "x"} is mapped again to @{text "x"}, and
  attempting to fix it again in the subsequent context is an error.
  Alternatively, fixed parameters can be renamed explicitly as
  follows: *}

ML {*
  val ctxt0 = @{context};
  val ([x1, x2, x3], ctxt1) =
    ctxt0 |> Variable.variant_fixes ["x", "x", "x"];
*}

text {* The following ML code can now work with the invented names of
  @{text x1}, @{text x2}, @{text x3}, without depending on
  the details on the system policy for introducing these variants.
  Recall that within a proof body the system always invents fresh
  ``skolem constants'', e.g.\ as follows: *}

notepad
begin
  ML_prf %"ML" {*
    val ctxt0 = @{context};

    val ([x1], ctxt1) = ctxt0 |> Variable.add_fixes ["x"];
    val ([x2], ctxt2) = ctxt1 |> Variable.add_fixes ["x"];
    val ([x3], ctxt3) = ctxt2 |> Variable.add_fixes ["x"];

    val ([y1, y2], ctxt4) =
      ctxt3 |> Variable.variant_fixes ["y", "y"];
  *}
end

text {* In this situation @{ML Variable.add_fixes} and @{ML
  Variable.variant_fixes} are very similar, but identical name
  proposals given in a row are only accepted by the second version.
  *}


section {* Assumptions \label{sec:assumptions} *}

text {*
  An \emph{assumption} is a proposition that it is postulated in the
  current context.  Local conclusions may use assumptions as
  additional facts, but this imposes implicit hypotheses that weaken
  the overall statement.

  Assumptions are restricted to fixed non-schematic statements, i.e.\
  all generality needs to be expressed by explicit quantifiers.
  Nevertheless, the result will be in HHF normal form with outermost
  quantifiers stripped.  For example, by assuming @{text "\<And>x :: \<alpha>. P
  x"} we get @{text "\<And>x :: \<alpha>. P x \<turnstile> P ?x"} for schematic @{text "?x"}
  of fixed type @{text "\<alpha>"}.  Local derivations accumulate more and
  more explicit references to hypotheses: @{text "A\<^isub>1, \<dots>,
  A\<^isub>n \<turnstile> B"} where @{text "A\<^isub>1, \<dots>, A\<^isub>n"} needs to
  be covered by the assumptions of the current context.

  \medskip The @{text "add_assms"} operation augments the context by
  local assumptions, which are parameterized by an arbitrary @{text
  "export"} rule (see below).

  The @{text "export"} operation moves facts from a (larger) inner
  context into a (smaller) outer context, by discharging the
  difference of the assumptions as specified by the associated export
  rules.  Note that the discharged portion is determined by the
  difference of contexts, not the facts being exported!  There is a
  separate flag to indicate a goal context, where the result is meant
  to refine an enclosing sub-goal of a structured proof state.

  \medskip The most basic export rule discharges assumptions directly
  by means of the @{text "\<Longrightarrow>"} introduction rule:
  \[
  \infer[(@{text "\<Longrightarrow>\<hyphen>intro"})]{@{text "\<Gamma> - A \<turnstile> A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \]

  The variant for goal refinements marks the newly introduced
  premises, which causes the canonical Isar goal refinement scheme to
  enforce unification with local premises within the goal:
  \[
  \infer[(@{text "#\<Longrightarrow>\<hyphen>intro"})]{@{text "\<Gamma> - A \<turnstile> #A \<Longrightarrow> B"}}{@{text "\<Gamma> \<turnstile> B"}}
  \]

  \medskip Alternative versions of assumptions may perform arbitrary
  transformations on export, as long as the corresponding portion of
  hypotheses is removed from the given facts.  For example, a local
  definition works by fixing @{text "x"} and assuming @{text "x \<equiv> t"},
  with the following export rule to reverse the effect:
  \[
  \infer[(@{text "\<equiv>\<hyphen>expand"})]{@{text "\<Gamma> - (x \<equiv> t) \<turnstile> B t"}}{@{text "\<Gamma> \<turnstile> B x"}}
  \]
  This works, because the assumption @{text "x \<equiv> t"} was introduced in
  a context with @{text "x"} being fresh, so @{text "x"} does not
  occur in @{text "\<Gamma>"} here.
*}

text %mlref {*
  \begin{mldecls}
  @{index_ML_type Assumption.export} \\
  @{index_ML Assumption.assume: "cterm -> thm"} \\
  @{index_ML Assumption.add_assms:
    "Assumption.export ->
  cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{index_ML Assumption.add_assumes: "
  cterm list -> Proof.context -> thm list * Proof.context"} \\
  @{index_ML Assumption.export: "bool -> Proof.context -> Proof.context -> thm -> thm"} \\
  \end{mldecls}

  \begin{description}

  \item Type @{ML_type Assumption.export} represents arbitrary export
  rules, which is any function of type @{ML_type "bool -> cterm list
  -> thm -> thm"}, where the @{ML_type "bool"} indicates goal mode,
  and the @{ML_type "cterm list"} the collection of assumptions to be
  discharged simultaneously.

  \item @{ML Assumption.assume}~@{text "A"} turns proposition @{text
  "A"} into a primitive assumption @{text "A \<turnstile> A'"}, where the
  conclusion @{text "A'"} is in HHF normal form.

  \item @{ML Assumption.add_assms}~@{text "r As"} augments the context
  by assumptions @{text "As"} with export rule @{text "r"}.  The
  resulting facts are hypothetical theorems as produced by the raw
  @{ML Assumption.assume}.

  \item @{ML Assumption.add_assumes}~@{text "As"} is a special case of
  @{ML Assumption.add_assms} where the export rule performs @{text
  "\<Longrightarrow>\<hyphen>intro"} or @{text "#\<Longrightarrow>\<hyphen>intro"}, depending on goal
  mode.

  \item @{ML Assumption.export}~@{text "is_goal inner outer thm"}
  exports result @{text "thm"} from the the @{text "inner"} context
  back into the @{text "outer"} one; @{text "is_goal = true"} means
  this is a goal context.  The result is in HHF normal form.  Note
  that @{ML "Proof_Context.export"} combines @{ML "Variable.export"}
  and @{ML "Assumption.export"} in the canonical way.

  \end{description}
*}

text %mlex {* The following example demonstrates how rules can be
  derived by building up a context of assumptions first, and exporting
  some local fact afterwards.  We refer to @{theory Pure} equality
  here for testing purposes.
*}

ML {*
  (*static compile-time context -- for testing only*)
  val ctxt0 = @{context};

  val ([eq], ctxt1) =
    ctxt0 |> Assumption.add_assumes [@{cprop "x \<equiv> y"}];
  val eq' = Thm.symmetric eq;

  (*back to original context -- discharges assumption*)
  val r = Assumption.export false ctxt1 ctxt0 eq';
*}

text {* Note that the variables of the resulting rule are not
  generalized.  This would have required to fix them properly in the
  context beforehand, and export wrt.\ variables afterwards (cf.\ @{ML
  Variable.export} or the combined @{ML "Proof_Context.export"}).  *}


section {* Structured goals and results \label{sec:struct-goals} *}

text {*
  Local results are established by monotonic reasoning from facts
  within a context.  This allows common combinations of theorems,
  e.g.\ via @{text "\<And>/\<Longrightarrow>"} elimination, resolution rules, or equational
  reasoning, see \secref{sec:thms}.  Unaccounted context manipulations
  should be avoided, notably raw @{text "\<And>/\<Longrightarrow>"} introduction or ad-hoc
  references to free variables or assumptions not present in the proof
  context.

  \medskip The @{text "SUBPROOF"} combinator allows to structure a
  tactical proof recursively by decomposing a selected sub-goal:
  @{text "(\<And>x. A(x) \<Longrightarrow> B(x)) \<Longrightarrow> \<dots>"} is turned into @{text "B(x) \<Longrightarrow> \<dots>"}
  after fixing @{text "x"} and assuming @{text "A(x)"}.  This means
  the tactic needs to solve the conclusion, but may use the premise as
  a local fact, for locally fixed variables.

  The family of @{text "FOCUS"} combinators is similar to @{text
  "SUBPROOF"}, but allows to retain schematic variables and pending
  subgoals in the resulting goal state.

  The @{text "prove"} operation provides an interface for structured
  backwards reasoning under program control, with some explicit sanity
  checks of the result.  The goal context can be augmented by
  additional fixed variables (cf.\ \secref{sec:variables}) and
  assumptions (cf.\ \secref{sec:assumptions}), which will be available
  as local facts during the proof and discharged into implications in
  the result.  Type and term variables are generalized as usual,
  according to the context.

  The @{text "obtain"} operation produces results by eliminating
  existing facts by means of a given tactic.  This acts like a dual
  conclusion: the proof demonstrates that the context may be augmented
  by parameters and assumptions, without affecting any conclusions
  that do not mention these parameters.  See also
  \cite{isabelle-isar-ref} for the user-level @{command obtain} and
  @{command guess} elements.  Final results, which may not refer to
  the parameters in the conclusion, need to exported explicitly into
  the original context.  *}

text %mlref {*
  \begin{mldecls}
  @{index_ML SELECT_GOAL: "tactic -> int -> tactic"} \\
  @{index_ML SUBPROOF: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{index_ML Subgoal.FOCUS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{index_ML Subgoal.FOCUS_PREMS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{index_ML Subgoal.FOCUS_PARAMS: "(Subgoal.focus -> tactic) ->
  Proof.context -> int -> tactic"} \\
  @{index_ML Subgoal.focus: "Proof.context -> int -> thm -> Subgoal.focus * thm"} \\
  @{index_ML Subgoal.focus_prems: "Proof.context -> int -> thm -> Subgoal.focus * thm"} \\
  @{index_ML Subgoal.focus_params: "Proof.context -> int -> thm -> Subgoal.focus * thm"} \\
  \end{mldecls}

  \begin{mldecls}
  @{index_ML Goal.prove: "Proof.context -> string list -> term list -> term ->
  ({prems: thm list, context: Proof.context} -> tactic) -> thm"} \\
  @{index_ML Goal.prove_multi: "Proof.context -> string list -> term list -> term list ->
  ({prems: thm list, context: Proof.context} -> tactic) -> thm list"} \\
  \end{mldecls}
  \begin{mldecls}
  @{index_ML Obtain.result: "(Proof.context -> tactic) -> thm list ->
  Proof.context -> ((string * cterm) list * thm list) * Proof.context"} \\
  \end{mldecls}

  \begin{description}

  \item @{ML SELECT_GOAL}~@{text "tac i"} confines a tactic to the
  specified subgoal @{text "i"}.  This introduces a nested goal state,
  without decomposing the internal structure of the subgoal yet.

  \item @{ML SUBPROOF}~@{text "tac ctxt i"} decomposes the structure
  of the specified sub-goal, producing an extended context and a
  reduced goal, which needs to be solved by the given tactic.  All
  schematic parameters of the goal are imported into the context as
  fixed ones, which may not be instantiated in the sub-proof.

  \item @{ML Subgoal.FOCUS}, @{ML Subgoal.FOCUS_PREMS}, and @{ML
  Subgoal.FOCUS_PARAMS} are similar to @{ML SUBPROOF}, but are
  slightly more flexible: only the specified parts of the subgoal are
  imported into the context, and the body tactic may introduce new
  subgoals and schematic variables.

  \item @{ML Subgoal.focus}, @{ML Subgoal.focus_prems}, @{ML
  Subgoal.focus_params} extract the focus information from a goal
  state in the same way as the corresponding tacticals above.  This is
  occasionally useful to experiment without writing actual tactics
  yet.

  \item @{ML Goal.prove}~@{text "ctxt xs As C tac"} states goal @{text
  "C"} in the context augmented by fixed variables @{text "xs"} and
  assumptions @{text "As"}, and applies tactic @{text "tac"} to solve
  it.  The latter may depend on the local assumptions being presented
  as facts.  The result is in HHF normal form.

  \item @{ML Goal.prove_multi} is simular to @{ML Goal.prove}, but
  states several conclusions simultaneously.  The goal is encoded by
  means of Pure conjunction; @{ML Goal.conjunction_tac} will turn this
  into a collection of individual subgoals.

  \item @{ML Obtain.result}~@{text "tac thms ctxt"} eliminates the
  given facts using a tactic, which results in additional fixed
  variables and assumptions in the context.  Final results need to be
  exported explicitly.

  \end{description}
*}

text %mlex {* The following minimal example illustrates how to access
  the focus information of a structured goal state. *}

notepad
begin
  fix A B C :: "'a \<Rightarrow> bool"

  have "\<And>x. A x \<Longrightarrow> B x \<Longrightarrow> C x"
    ML_val
    {*
      val {goal, context = goal_ctxt, ...} = @{Isar.goal};
      val (focus as {params, asms, concl, ...}, goal') =
        Subgoal.focus goal_ctxt 1 goal;
      val [A, B] = #prems focus;
      val [(_, x)] = #params focus;
    *}
    oops

text {* \medskip The next example demonstrates forward-elimination in
  a local context, using @{ML Obtain.result}.  *}

notepad
begin
  assume ex: "\<exists>x. B x"

  ML_prf %"ML" {*
    val ctxt0 = @{context};
    val (([(_, x)], [B]), ctxt1) = ctxt0
      |> Obtain.result (fn _ => etac @{thm exE} 1) [@{thm ex}];
  *}
  ML_prf %"ML" {*
    singleton (Proof_Context.export ctxt1 ctxt0) @{thm refl};
  *}
  ML_prf %"ML" {*
    Proof_Context.export ctxt1 ctxt0 [Thm.reflexive x]
      handle ERROR msg => (warning msg; []);
  *}
end

end
