(*:maxLineLen=78:*)

theory Isar
imports Base
begin

chapter \<open>Isar language elements\<close>

text \<open>
  The Isar proof language (see also @{cite \<open>\S2\<close> "isabelle-isar-ref"})
  consists of three main categories of language elements:

  \<^enum> Proof \<^emph>\<open>commands\<close> define the primary language of transactions of the
  underlying Isar/VM interpreter. Typical examples are @{command "fix"},
  @{command "assume"}, @{command "show"}, @{command "proof"}, and @{command
  "qed"}.

  Composing proof commands according to the rules of the Isar/VM leads to
  expressions of structured proof text, such that both the machine and the
  human reader can give it a meaning as formal reasoning.

  \<^enum> Proof \<^emph>\<open>methods\<close> define a secondary language of mixed forward-backward
  refinement steps involving facts and goals. Typical examples are @{method
  rule}, @{method unfold}, and @{method simp}.

  Methods can occur in certain well-defined parts of the Isar proof language,
  say as arguments to @{command "proof"}, @{command "qed"}, or @{command
  "by"}.

  \<^enum> \<^emph>\<open>Attributes\<close> define a tertiary language of small annotations to theorems
  being defined or referenced. Attributes can modify both the context and the
  theorem.

  Typical examples are @{attribute intro} (which affects the context), and
  @{attribute symmetric} (which affects the theorem).
\<close>


section \<open>Proof commands\<close>

text \<open>
  A \<^emph>\<open>proof command\<close> is state transition of the Isar/VM proof interpreter.

  In principle, Isar proof commands could be defined in user-space as well.
  The system is built like that in the first place: one part of the commands
  are primitive, the other part is defined as derived elements. Adding to the
  genuine structured proof language requires profound understanding of the
  Isar/VM machinery, though, so this is beyond the scope of this manual.

  What can be done realistically is to define some diagnostic commands that
  inspect the general state of the Isar/VM, and report some feedback to the
  user. Typically this involves checking of the linguistic \<^emph>\<open>mode\<close> of a proof
  state, or peeking at the pending goals (if available).

  Another common application is to define a toplevel command that poses a
  problem to the user as Isar proof state and processes the final result
  relatively to the context. Thus a proof can be incorporated into the context
  of some user-space tool, without modifying the Isar proof language itself.
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Proof.state} \\
  @{define_ML Proof.assert_forward: "Proof.state -> Proof.state"} \\
  @{define_ML Proof.assert_chain: "Proof.state -> Proof.state"} \\
  @{define_ML Proof.assert_backward: "Proof.state -> Proof.state"} \\
  @{define_ML Proof.simple_goal: "Proof.state -> {context: Proof.context, goal: thm}"} \\
  @{define_ML Proof.goal: "Proof.state ->
  {context: Proof.context, facts: thm list, goal: thm}"} \\
  @{define_ML Proof.raw_goal: "Proof.state ->
  {context: Proof.context, facts: thm list, goal: thm}"} \\
  @{define_ML Proof.theorem: "Method.text option ->
  (thm list list -> Proof.context -> Proof.context) ->
  (term * term list) list list -> Proof.context -> Proof.state"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Proof.state\<close> represents Isar proof states. This is a
  block-structured configuration with proof context, linguistic mode, and
  optional goal. The latter consists of goal context, goal facts
  (``\<open>using\<close>''), and tactical goal state (see \secref{sec:tactical-goals}).

  The general idea is that the facts shall contribute to the refinement of
  some parts of the tactical goal --- how exactly is defined by the proof
  method that is applied in that situation.

  \<^descr> \<^ML>\<open>Proof.assert_forward\<close>, \<^ML>\<open>Proof.assert_chain\<close>, \<^ML>\<open>Proof.assert_backward\<close> are partial identity functions that fail unless a
  certain linguistic mode is active, namely ``\<open>proof(state)\<close>'',
  ``\<open>proof(chain)\<close>'', ``\<open>proof(prove)\<close>'', respectively (using the terminology
  of @{cite "isabelle-isar-ref"}).

  It is advisable study the implementations of existing proof commands for
  suitable modes to be asserted.

  \<^descr> \<^ML>\<open>Proof.simple_goal\<close>~\<open>state\<close> returns the structured Isar goal (if
  available) in the form seen by ``simple'' methods (like @{method simp} or
  @{method blast}). The Isar goal facts are already inserted as premises into
  the subgoals, which are presented individually as in \<^ML>\<open>Proof.goal\<close>.

  \<^descr> \<^ML>\<open>Proof.goal\<close>~\<open>state\<close> returns the structured Isar goal (if available)
  in the form seen by regular methods (like @{method rule}). The auxiliary
  internal encoding of Pure conjunctions is split into individual subgoals as
  usual.

  \<^descr> \<^ML>\<open>Proof.raw_goal\<close>~\<open>state\<close> returns the structured Isar goal (if
  available) in the raw internal form seen by ``raw'' methods (like @{method
  induct}). This form is rarely appropriate for diagnostic tools; \<^ML>\<open>Proof.simple_goal\<close> or \<^ML>\<open>Proof.goal\<close> should be used in most situations.

  \<^descr> \<^ML>\<open>Proof.theorem\<close>~\<open>before_qed after_qed statement ctxt\<close> initializes a
  toplevel Isar proof state within a given context.

  The optional \<open>before_qed\<close> method is applied at the end of the proof, just
  before extracting the result (this feature is rarely used).

  The \<open>after_qed\<close> continuation receives the extracted result in order to apply
  it to the final context in a suitable way (e.g.\ storing named facts). Note
  that at this generic level the target context is specified as \<^ML_type>\<open>Proof.context\<close>, but the usual wrapping of toplevel proofs into command
  transactions will provide a \<^ML_type>\<open>local_theory\<close> here
  (\chref{ch:local-theory}). This affects the way how results are stored.

  The \<open>statement\<close> is given as a nested list of terms, each associated with
  optional @{keyword "is"} patterns as usual in the Isar source language. The
  original nested list structure over terms is turned into one over theorems
  when \<open>after_qed\<close> is invoked.
\<close>


text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "Isar.goal"} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^descr> \<open>@{Isar.goal}\<close> refers to the regular goal state (if available) of the
  current proof state managed by the Isar toplevel --- as abstract value.

  This only works for diagnostic ML commands, such as @{command ML_val} or
  @{command ML_command}.
\<close>

text %mlex \<open>
  The following example peeks at a certain goal configuration.
\<close>

notepad
begin
  have A and B and C
    ML_val
     \<open>val n = Thm.nprems_of (#goal @{Isar.goal});
      \<^assert> (n = 3);\<close>
    sorry
end

text \<open>
  Here we see 3 individual subgoals in the same way as regular proof methods
  would do.
\<close>


section \<open>Proof methods\<close>

text \<open>
  A \<open>method\<close> is a function \<open>thm\<^sup>* \<rightarrow> context * goal \<rightarrow> (context \<times> goal)\<^sup>*\<^sup>*\<close>
  that operates on the full Isar goal configuration with context, goal facts,
  and tactical goal state and enumerates possible follow-up goal states. Under
  normal circumstances, the goal context remains unchanged, but it is also
  possible to declare named extensions of the proof context (\<^emph>\<open>cases\<close>).

  This means a proof method is like a structurally enhanced tactic (cf.\
  \secref{sec:tactics}). The well-formedness conditions for tactics need to
  hold for methods accordingly, with the following additions.

  \<^item> Goal addressing is further limited either to operate uniformly on \<^emph>\<open>all\<close>
  subgoals, or specifically on the \<^emph>\<open>first\<close> subgoal.

  Exception: old-style tactic emulations that are embedded into the method
  space, e.g.\ @{method rule_tac}.

  \<^item> A non-trivial method always needs to make progress: an identical follow-up
  goal state has to be avoided.\<^footnote>\<open>This enables the user to write method
  expressions like \<open>meth\<^sup>+\<close> without looping, while the trivial do-nothing case
  can be recovered via \<open>meth\<^sup>?\<close>.\<close>

  Exception: trivial stuttering steps, such as ``@{method -}'' or @{method
  succeed}.

  \<^item> Goal facts passed to the method must not be ignored. If there is no
  sensible use of facts outside the goal state, facts should be inserted into
  the subgoals that are addressed by the method.


  \<^medskip>
  Syntactically, the language of proof methods appears as arguments to Isar
  commands like @{command "by"} or @{command apply}. User-space additions are
  reasonably easy by plugging suitable method-valued parser functions into the
  framework, using the @{command method_setup} command, for example.

  To get a better idea about the range of possibilities, consider the
  following Isar proof schemes. This is the general form of structured proof
  text:

  \<^medskip>
  \begin{tabular}{l}
  @{command from}~\<open>facts\<^sub>1\<close>~@{command have}~\<open>props\<close>~@{command using}~\<open>facts\<^sub>2\<close> \\
  @{command proof}~\<open>(initial_method)\<close> \\
  \quad\<open>body\<close> \\
  @{command qed}~\<open>(terminal_method)\<close> \\
  \end{tabular}
  \<^medskip>

  The goal configuration consists of \<open>facts\<^sub>1\<close> and \<open>facts\<^sub>2\<close> appended in that
  order, and various \<open>props\<close> being claimed. The \<open>initial_method\<close> is invoked
  with facts and goals together and refines the problem to something that is
  handled recursively in the proof \<open>body\<close>. The \<open>terminal_method\<close> has another
  chance to finish any remaining subgoals, but it does not see the facts of
  the initial step.

  \<^medskip>
  This pattern illustrates unstructured proof scripts:

  \<^medskip>
  \begin{tabular}{l}
  @{command have}~\<open>props\<close> \\
  \quad@{command using}~\<open>facts\<^sub>1\<close>~@{command apply}~\<open>method\<^sub>1\<close> \\
  \quad@{command apply}~\<open>method\<^sub>2\<close> \\
  \quad@{command using}~\<open>facts\<^sub>3\<close>~@{command apply}~\<open>method\<^sub>3\<close> \\
  \quad@{command done} \\
  \end{tabular}
  \<^medskip>

  The \<open>method\<^sub>1\<close> operates on the original claim while using \<open>facts\<^sub>1\<close>. Since
  the @{command apply} command structurally resets the facts, the \<open>method\<^sub>2\<close>
  will operate on the remaining goal state without facts. The \<open>method\<^sub>3\<close> will
  see again a collection of \<open>facts\<^sub>3\<close> that has been inserted into the script
  explicitly.

  \<^medskip>
  Empirically, any Isar proof method can be categorized as follows.

    \<^enum> \<^emph>\<open>Special method with cases\<close> with named context additions associated
    with the follow-up goal state.

    Example: @{method "induct"}, which is also a ``raw'' method since it
    operates on the internal representation of simultaneous claims as Pure
    conjunction (\secref{sec:logic-aux}), instead of separate subgoals
    (\secref{sec:tactical-goals}).

    \<^enum> \<^emph>\<open>Structured method\<close> with strong emphasis on facts outside the goal
    state.

    Example: @{method "rule"}, which captures the key ideas behind structured
    reasoning in Isar in its purest form.

    \<^enum> \<^emph>\<open>Simple method\<close> with weaker emphasis on facts, which are inserted into
    subgoals to emulate old-style tactical ``premises''.

    Examples: @{method "simp"}, @{method "blast"}, @{method "auto"}.

    \<^enum> \<^emph>\<open>Old-style tactic emulation\<close> with detailed numeric goal addressing and
    explicit references to entities of the internal goal state (which are
    otherwise invisible from proper Isar proof text). The naming convention
    \<open>foo_tac\<close> makes this special non-standard status clear.

    Example: @{method "rule_tac"}.

  When implementing proof methods, it is advisable to study existing
  implementations carefully and imitate the typical ``boiler plate'' for
  context-sensitive parsing and further combinators to wrap-up tactic
  expressions as methods.\<^footnote>\<open>Aliases or abbreviations of the standard method
  combinators should be avoided. Note that from Isabelle99 until Isabelle2009
  the system did provide various odd combinations of method syntax wrappers
  that made applications more complicated than necessary.\<close>
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type Proof.method} \\
  @{define_ML CONTEXT_METHOD: "(thm list -> context_tactic) -> Proof.method"} \\
  @{define_ML METHOD: "(thm list -> tactic) -> Proof.method"} \\
  @{define_ML SIMPLE_METHOD: "tactic -> Proof.method"} \\
  @{define_ML SIMPLE_METHOD': "(int -> tactic) -> Proof.method"} \\
  @{define_ML Method.insert_tac: "Proof.context -> thm list -> int -> tactic"} \\
  @{define_ML Method.setup: "binding -> (Proof.context -> Proof.method) context_parser ->
  string -> theory -> theory"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>Proof.method\<close> represents proof methods as abstract type.

  \<^descr> \<^ML>\<open>CONTEXT_METHOD\<close>~\<open>(fn facts => context_tactic)\<close> wraps \<open>context_tactic\<close>
  depending on goal facts as a general proof method that may change the proof
  context dynamically. A typical operation is \<^ML>\<open>Proof_Context.update_cases\<close>, which is wrapped up as combinator @{define_ML
  CONTEXT_CASES} for convenience.

  \<^descr> \<^ML>\<open>METHOD\<close>~\<open>(fn facts => tactic)\<close> wraps \<open>tactic\<close> depending on goal facts
  as regular proof method; the goal context is passed via method syntax.

  \<^descr> \<^ML>\<open>SIMPLE_METHOD\<close>~\<open>tactic\<close> wraps a tactic that addresses all subgoals
  uniformly as simple proof method. Goal facts are already inserted into all
  subgoals before \<open>tactic\<close> is applied.

  \<^descr> \<^ML>\<open>SIMPLE_METHOD'\<close>~\<open>tactic\<close> wraps a tactic that addresses a specific
  subgoal as simple proof method that operates on subgoal 1. Goal facts are
  inserted into the subgoal then the \<open>tactic\<close> is applied.

  \<^descr> \<^ML>\<open>Method.insert_tac\<close>~\<open>ctxt facts i\<close> inserts \<open>facts\<close> into subgoal \<open>i\<close>.
  This is convenient to reproduce part of the \<^ML>\<open>SIMPLE_METHOD\<close> or \<^ML>\<open>SIMPLE_METHOD'\<close> wrapping within regular \<^ML>\<open>METHOD\<close>, for example.

  \<^descr> \<^ML>\<open>Method.setup\<close>~\<open>name parser description\<close> provides the functionality of
  the Isar command @{command method_setup} as ML function.
\<close>

text %mlex \<open>
  See also @{command method_setup} in @{cite "isabelle-isar-ref"} which
  includes some abstract examples.

  \<^medskip>
  The following toy examples illustrate how the goal facts and state are
  passed to proof methods. The predefined proof method called ``@{method
  tactic}'' wraps ML source of type \<^ML_type>\<open>tactic\<close> (abstracted over
  \<^ML_text>\<open>facts\<close>). This allows immediate experimentation without parsing of
  concrete syntax.
\<close>

notepad
begin
  fix A B :: bool
  assume a: A and b: B

  have "A \<and> B"
    apply (tactic \<open>resolve_tac \<^context> @{thms conjI} 1\<close>)
    using a apply (tactic \<open>resolve_tac \<^context> facts 1\<close>)
    using b apply (tactic \<open>resolve_tac \<^context> facts 1\<close>)
    done

  have "A \<and> B"
    using a and b
    ML_val \<open>@{Isar.goal}\<close>
    apply (tactic \<open>Method.insert_tac \<^context> facts 1\<close>)
    apply (tactic \<open>(resolve_tac \<^context> @{thms conjI} THEN_ALL_NEW assume_tac \<^context>) 1\<close>)
    done
end

text \<open>
  \<^medskip>
  The next example implements a method that simplifies the first subgoal by
  rewrite rules that are given as arguments.
\<close>

method_setup my_simp =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (asm_full_simp_tac
        (put_simpset HOL_basic_ss ctxt addsimps thms) i)))\<close>
  "rewrite subgoal by given rules"

text \<open>
  The concrete syntax wrapping of @{command method_setup} always
  passes-through the proof context at the end of parsing, but it is not used
  in this example.

  The \<^ML>\<open>Attrib.thms\<close> parser produces a list of theorems from the usual Isar
  syntax involving attribute expressions etc.\ (syntax category @{syntax
  thms}) @{cite "isabelle-isar-ref"}. The resulting \<^ML_text>\<open>thms\<close> are
  added to \<^ML>\<open>HOL_basic_ss\<close> which already contains the basic Simplifier
  setup for HOL.

  The tactic \<^ML>\<open>asm_full_simp_tac\<close> is the one that is also used in method
  @{method simp} by default. The extra wrapping by the \<^ML>\<open>CHANGED\<close> tactical
  ensures progress of simplification: identical goal states are filtered out
  explicitly to make the raw tactic conform to standard Isar method behaviour.

  \<^medskip>
  Method @{method my_simp} can be used in Isar proofs like this:
\<close>

notepad
begin
  fix a b c :: 'a
  assume a: "a = b"
  assume b: "b = c"
  have "a = c" by (my_simp a b)
end

text \<open>
  Here is a similar method that operates on all subgoals, instead of just the
  first one.\<close>

method_setup my_simp_all =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    SIMPLE_METHOD
      (CHANGED
        (ALLGOALS (asm_full_simp_tac
          (put_simpset HOL_basic_ss ctxt addsimps thms)))))\<close>
  "rewrite all subgoals by given rules"

notepad
begin
  fix a b c :: 'a
  assume a: "a = b"
  assume b: "b = c"
  have "a = c" and "c = b" by (my_simp_all a b)
end

text \<open>
  \<^medskip>
  Apart from explicit arguments, common proof methods typically work with a
  default configuration provided by the context. As a shortcut to rule
  management we use a cheap solution via the @{command named_theorems} command
  to declare a dynamic fact in the context.
\<close>

named_theorems my_simp

text \<open>
  The proof method is now defined as before, but we append the explicit
  arguments and the rules from the context.
\<close>

method_setup my_simp' =
  \<open>Attrib.thms >> (fn thms => fn ctxt =>
    let
      val my_simps = Named_Theorems.get ctxt \<^named_theorems>\<open>my_simp\<close>
    in
      SIMPLE_METHOD' (fn i =>
        CHANGED (asm_full_simp_tac
          (put_simpset HOL_basic_ss ctxt
            addsimps (thms @ my_simps)) i))
    end)\<close>
  "rewrite subgoal by given rules and my_simp rules from the context"

text \<open>
  \<^medskip>
  Method @{method my_simp'} can be used in Isar proofs like this:
\<close>

notepad
begin
  fix a b c :: 'a
  assume [my_simp]: "a \<equiv> b"
  assume [my_simp]: "b \<equiv> c"
  have "a \<equiv> c" by my_simp'
end

text \<open>
  \<^medskip>
  The @{method my_simp} variants defined above are ``simple'' methods, i.e.\
  the goal facts are merely inserted as goal premises by the \<^ML>\<open>SIMPLE_METHOD'\<close> or \<^ML>\<open>SIMPLE_METHOD\<close> wrapper. For proof methods that are
  similar to the standard collection of @{method simp}, @{method blast},
  @{method fast}, @{method auto} there is little more that can be done.

  Note that using the primary goal facts in the same manner as the method
  arguments obtained via concrete syntax or the context does not meet the
  requirement of ``strong emphasis on facts'' of regular proof methods,
  because rewrite rules as used above can be easily ignored. A proof text
  ``@{command using}~\<open>foo\<close>~@{command "by"}~\<open>my_simp\<close>'' where \<open>foo\<close> is not used
  would deceive the reader.

  \<^medskip>
  The technical treatment of rules from the context requires further
  attention. Above we rebuild a fresh \<^ML_type>\<open>simpset\<close> from the arguments
  and \<^emph>\<open>all\<close> rules retrieved from the context on every invocation of the
  method. This does not scale to really large collections of rules, which
  easily emerges in the context of a big theory library, for example.

  This is an inherent limitation of the simplistic rule management via
  @{command named_theorems}, because it lacks tool-specific storage and
  retrieval. More realistic applications require efficient index-structures
  that organize theorems in a customized manner, such as a discrimination net
  that is indexed by the left-hand sides of rewrite rules. For variations on
  the Simplifier, re-use of the existing type \<^ML_type>\<open>simpset\<close> is adequate,
  but scalability would require it be maintained statically within the context
  data, not dynamically on each tool invocation.
\<close>


section \<open>Attributes \label{sec:attributes}\<close>

text \<open>
  An \<^emph>\<open>attribute\<close> is a function \<open>context \<times> thm \<rightarrow> context \<times> thm\<close>, which means
  both a (generic) context and a theorem can be modified simultaneously. In
  practice this mixed form is very rare, instead attributes are presented
  either as \<^emph>\<open>declaration attribute:\<close> \<open>thm \<rightarrow> context \<rightarrow> context\<close> or \<^emph>\<open>rule
  attribute:\<close> \<open>context \<rightarrow> thm \<rightarrow> thm\<close>.

  Attributes can have additional arguments via concrete syntax. There is a
  collection of context-sensitive parsers for various logical entities (types,
  terms, theorems). These already take care of applying morphisms to the
  arguments when attribute expressions are moved into a different context (see
  also \secref{sec:morphisms}).

  When implementing declaration attributes, it is important to operate exactly
  on the variant of the generic context that is provided by the system, which
  is either global theory context or local proof context. In particular, the
  background theory of a local context must not be modified in this
  situation!
\<close>

text %mlref \<open>
  \begin{mldecls}
  @{define_ML_type attribute} \\
  @{define_ML Thm.rule_attribute: "thm list ->
  (Context.generic -> thm -> thm) -> attribute"} \\
  @{define_ML Thm.declaration_attribute: "
  (thm -> Context.generic -> Context.generic) -> attribute"} \\
  @{define_ML Attrib.setup: "binding -> attribute context_parser ->
  string -> theory -> theory"} \\
  \end{mldecls}

  \<^descr> Type \<^ML_type>\<open>attribute\<close> represents attributes as concrete type alias.

  \<^descr> \<^ML>\<open>Thm.rule_attribute\<close>~\<open>thms (fn context => rule)\<close> wraps a
  context-dependent rule (mapping on \<^ML_type>\<open>thm\<close>) as attribute.

  The \<open>thms\<close> are additional parameters: when forming an abstract closure, the
  system may provide dummy facts that are propagated according to strict
  evaluation discipline. In that case, \<open>rule\<close> is bypassed.

  \<^descr> \<^ML>\<open>Thm.declaration_attribute\<close>~\<open>(fn thm => decl)\<close> wraps a
  theorem-dependent declaration (mapping on \<^ML_type>\<open>Context.generic\<close>) as
  attribute.

  When forming an abstract closure, the system may provide a dummy fact as
  \<open>thm\<close>. In that case, \<open>decl\<close> is bypassed.

  \<^descr> \<^ML>\<open>Attrib.setup\<close>~\<open>name parser description\<close> provides the functionality of
  the Isar command @{command attribute_setup} as ML function.
\<close>

text %mlantiq \<open>
  \begin{matharray}{rcl}
  @{ML_antiquotation_def attributes} & : & \<open>ML_antiquotation\<close> \\
  \end{matharray}

  \<^rail>\<open>
  @@{ML_antiquotation attributes} attributes
  \<close>

  \<^descr> \<open>@{attributes [\<dots>]}\<close> embeds attribute source representation into the ML
  text, which is particularly useful with declarations like \<^ML>\<open>Local_Theory.note\<close>. Attribute names are internalized at compile time, but
  the source is unevaluated. This means attributes with formal arguments
  (types, terms, theorems) may be subject to odd effects of dynamic scoping!
\<close>

text %mlex \<open>
  See also @{command attribute_setup} in @{cite "isabelle-isar-ref"} which
  includes some abstract examples.
\<close>

end
