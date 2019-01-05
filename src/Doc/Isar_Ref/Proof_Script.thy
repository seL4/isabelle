(*:maxLineLen=78:*)

theory Proof_Script
  imports Main Base
begin

chapter \<open>Proof scripts\<close>

text \<open>
  Interactive theorem proving is traditionally associated with ``proof
  scripts'', but Isabelle/Isar is centered around structured \<^emph>\<open>proof
  documents\<close> instead (see also \chref{ch:proofs}).

  Nonetheless, it is possible to emulate proof scripts by sequential
  refinements of a proof state in backwards mode, notably with the @{command
  apply} command (see \secref{sec:tactic-commands}).

  There are also various proof methods that allow to refer to implicit goal
  state information that is not accessible to structured Isar proofs (see
  \secref{sec:tactics}). Note that the @{command subgoal}
  (\secref{sec:subgoal}) command usually eliminates the need for implicit goal
  state references.
\<close>


section \<open>Commands for step-wise refinement \label{sec:tactic-commands}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "supply"}\<open>\<^sup>*\<close> & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{command_def "apply"}\<open>\<^sup>*\<close> & : & \<open>proof(prove) \<rightarrow> proof(prove)\<close> \\
    @{command_def "apply_end"}\<open>\<^sup>*\<close> & : & \<open>proof(state) \<rightarrow> proof(state)\<close> \\
    @{command_def "done"}\<open>\<^sup>*\<close> & : & \<open>proof(prove) \<rightarrow> proof(state) | local_theory | theory\<close> \\
    @{command_def "defer"}\<open>\<^sup>*\<close> & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "prefer"}\<open>\<^sup>*\<close> & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "back"}\<open>\<^sup>*\<close> & : & \<open>proof \<rightarrow> proof\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command supply} (@{syntax thmdef}? @{syntax thms} + @'and')
    ;
    ( @@{command apply} | @@{command apply_end} ) @{syntax method}
    ;
    @@{command defer} @{syntax nat}?
    ;
    @@{command prefer} @{syntax nat}
  \<close>

  \<^descr> @{command "supply"} supports fact definitions during goal refinement: it
  is similar to @{command "note"}, but it operates in backwards mode and does
  not have any impact on chained facts.

  \<^descr> @{command "apply"}~\<open>m\<close> applies proof method \<open>m\<close> in initial position, but
  unlike @{command "proof"} it retains ``\<open>proof(prove)\<close>'' mode. Thus
  consecutive method applications may be given just as in tactic scripts.

  Facts are passed to \<open>m\<close> as indicated by the goal's forward-chain mode, and
  are \<^emph>\<open>consumed\<close> afterwards. Thus any further @{command "apply"} command
  would always work in a purely backward manner.

  \<^descr> @{command "apply_end"}~\<open>m\<close> applies proof method \<open>m\<close> as if in terminal
  position. Basically, this simulates a multi-step tactic script for @{command
  "qed"}, but may be given anywhere within the proof body.

  No facts are passed to \<open>m\<close> here. Furthermore, the static context is that of
  the enclosing goal (as for actual @{command "qed"}). Thus the proof method
  may not refer to any assumptions introduced in the current body, for
  example.

  \<^descr> @{command "done"} completes a proof script, provided that the current goal
  state is solved completely. Note that actual structured proof commands
  (e.g.\ ``@{command "."}'' or @{command "sorry"}) may be used to conclude
  proof scripts as well.

  \<^descr> @{command "defer"}~\<open>n\<close> and @{command "prefer"}~\<open>n\<close> shuffle the list of
  pending goals: @{command "defer"} puts off sub-goal \<open>n\<close> to the end of the
  list (\<open>n = 1\<close> by default), while @{command "prefer"} brings sub-goal \<open>n\<close> to
  the front.

  \<^descr> @{command "back"} does back-tracking over the result sequence of the
  latest proof command. Any proof command may return multiple results, and
  this command explores the possibilities step-by-step. It is mainly useful
  for experimentation and interactive exploration, and should be avoided in
  finished proofs.
\<close>


section \<open>Explicit subgoal structure \label{sec:subgoal}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "subgoal"}\<open>\<^sup>*\<close> & : & \<open>proof \<rightarrow> proof\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command subgoal} @{syntax thmbind}? prems? params?
    ;
    prems: @'premises' @{syntax thmbind}?
    ;
    params: @'for' '\<dots>'? (('_' | @{syntax name})+)
  \<close>

  \<^descr> @{command "subgoal"} allows to impose some structure on backward
  refinements, to avoid proof scripts degenerating into long of @{command
  apply} sequences.

  The current goal state, which is essentially a hidden part of the Isar/VM
  configuration, is turned into a proof context and remaining conclusion.
  This corresponds to @{command fix}~/ @{command assume}~/ @{command show} in
  structured proofs, but the text of the parameters, premises and conclusion
  is not given explicitly.

  Goal parameters may be specified separately, in order to allow referring to
  them in the proof body: ``@{command subgoal}~@{keyword "for"}~\<open>x y z\<close>''
  names a \<^emph>\<open>prefix\<close>, and ``@{command subgoal}~@{keyword "for"}~\<open>\<dots> x y z\<close>''
  names a \<^emph>\<open>suffix\<close> of goal parameters. The latter uses a literal \<^verbatim>\<open>\<dots>\<close> symbol
  as notation. Parameter positions may be skipped via dummies (underscore).
  Unspecified names remain internal, and thus inaccessible in the proof text.

  ``@{command subgoal}~@{keyword "premises"}~\<open>prems\<close>'' indicates that goal
  premises should be turned into assumptions of the context (otherwise the
  remaining conclusion is a Pure implication). The fact name and attributes
  are optional; the particular name ``\<open>prems\<close>'' is a common convention for the
  premises of an arbitrary goal context in proof scripts.

  ``@{command subgoal}~\<open>result\<close>'' indicates a fact name for the result of a
  proven subgoal. Thus it may be re-used in further reasoning, similar to the
  result of @{command show} in structured Isar proofs.


  Here are some abstract examples:
\<close>

lemma "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z"
  and "\<And>u v. X u \<Longrightarrow> Y v"
  subgoal \<proof>
  subgoal \<proof>
  done

lemma "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z"
  and "\<And>u v. X u \<Longrightarrow> Y v"
  subgoal for x y z \<proof>
  subgoal for u v \<proof>
  done

lemma "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z"
  and "\<And>u v. X u \<Longrightarrow> Y v"
  subgoal premises for x y z
    using \<open>A x\<close> \<open>B y\<close>
    \<proof>
  subgoal premises for u v
    using \<open>X u\<close>
    \<proof>
  done

lemma "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z"
  and "\<And>u v. X u \<Longrightarrow> Y v"
  subgoal r premises prems for x y z
  proof -
    have "A x" by (fact prems)
    moreover have "B y" by (fact prems)
    ultimately show ?thesis \<proof>
  qed
  subgoal premises prems for u v
  proof -
    have "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z" by (fact r)
    moreover
    have "X u" by (fact prems)
    ultimately show ?thesis \<proof>
  qed
  done

lemma "\<And>x y z. A x \<Longrightarrow> B y \<Longrightarrow> C z"
  subgoal premises prems for \<dots> z
  proof -
    from prems show "C z" \<proof>
  qed
  done


section \<open>Tactics: improper proof methods \label{sec:tactics}\<close>

text \<open>
  The following improper proof methods emulate traditional tactics. These
  admit direct access to the goal state, which is normally considered harmful!
  In particular, this may involve both numbered goal addressing (default 1),
  and dynamic instantiation within the scope of some subgoal.

  \begin{warn}
    Dynamic instantiations refer to universally quantified parameters of a
    subgoal (the dynamic context) rather than fixed variables and term
    abbreviations of a (static) Isar context.
  \end{warn}

  Tactic emulation methods, unlike their ML counterparts, admit simultaneous
  instantiation from both dynamic and static contexts. If names occur in both
  contexts goal parameters hide locally fixed variables. Likewise, schematic
  variables refer to term abbreviations, if present in the static context.
  Otherwise the schematic variable is interpreted as a schematic variable and
  left to be solved by unification with certain parts of the subgoal.

  Note that the tactic emulation proof methods in Isabelle/Isar are
  consistently named \<open>foo_tac\<close>. Note also that variable names occurring on
  left hand sides of instantiations must be preceded by a question mark if
  they coincide with a keyword or contain dots. This is consistent with the
  attribute @{attribute "where"} (see \secref{sec:pure-meth-att}).

  \begin{matharray}{rcl}
    @{method_def rule_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def erule_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def drule_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def frule_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def cut_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def thin_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def subgoal_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def rename_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def rotate_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def tactic}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def raw_tactic}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{method rule_tac} | @@{method erule_tac} | @@{method drule_tac} |
      @@{method frule_tac} | @@{method cut_tac}) @{syntax goal_spec}? \<newline>
    (@{syntax named_insts} @{syntax for_fixes} @'in' @{syntax thm} | @{syntax thms} )
    ;
    @@{method thin_tac} @{syntax goal_spec}? @{syntax prop} @{syntax for_fixes}
    ;
    @@{method subgoal_tac} @{syntax goal_spec}? (@{syntax prop} +) @{syntax for_fixes}
    ;
    @@{method rename_tac} @{syntax goal_spec}? (@{syntax name} +)
    ;
    @@{method rotate_tac} @{syntax goal_spec}? @{syntax int}?
    ;
    (@@{method tactic} | @@{method raw_tactic}) @{syntax text}
  \<close>

  \<^descr> @{method rule_tac} etc. do resolution of rules with explicit
  instantiation. This works the same way as the ML tactics \<^ML>\<open>Rule_Insts.res_inst_tac\<close> etc.\ (see @{cite "isabelle-implementation"}).

  Multiple rules may be only given if there is no instantiation; then @{method
  rule_tac} is the same as \<^ML>\<open>resolve_tac\<close> in ML (see @{cite
  "isabelle-implementation"}).

  \<^descr> @{method cut_tac} inserts facts into the proof state as assumption of a
  subgoal; instantiations may be given as well. Note that the scope of
  schematic variables is spread over the main goal statement and rule premises
  are turned into new subgoals. This is in contrast to the regular method
  @{method insert} which inserts closed rule statements.

  \<^descr> @{method thin_tac}~\<open>\<phi>\<close> deletes the specified premise from a subgoal. Note
  that \<open>\<phi>\<close> may contain schematic variables, to abbreviate the intended
  proposition; the first matching subgoal premise will be deleted. Removing
  useless premises from a subgoal increases its readability and can make
  search tactics run faster.

  \<^descr> @{method subgoal_tac}~\<open>\<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close> adds the propositions \<open>\<phi>\<^sub>1 \<dots> \<phi>\<^sub>n\<close> as
  local premises to a subgoal, and poses the same as new subgoals (in the
  original context).

  \<^descr> @{method rename_tac}~\<open>x\<^sub>1 \<dots> x\<^sub>n\<close> renames parameters of a goal according to
  the list \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close>, which refers to the \<^emph>\<open>suffix\<close> of variables.

  \<^descr> @{method rotate_tac}~\<open>n\<close> rotates the premises of a subgoal by \<open>n\<close>
  positions: from right to left if \<open>n\<close> is positive, and from left to right if
  \<open>n\<close> is negative; the default value is 1.

  \<^descr> @{method tactic}~\<open>text\<close> produces a proof method from any ML text of type
  \<^ML_type>\<open>tactic\<close>. Apart from the usual ML environment and the current proof
  context, the ML code may refer to the locally bound values \<^ML_text>\<open>facts\<close>,
  which indicates any current facts used for forward-chaining.

  \<^descr> @{method raw_tactic} is similar to @{method tactic}, but presents the goal
  state in its raw internal form, where simultaneous subgoals appear as
  conjunction of the logical framework instead of the usual split into several
  subgoals. While feature this is useful for debugging of complex method
  definitions, it should not never appear in production theories.
\<close>

end
