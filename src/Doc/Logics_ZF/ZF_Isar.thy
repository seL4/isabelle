theory ZF_Isar
imports ZF
begin

(*<*)
ML_file "../antiquote_setup.ML"
(*>*)

chapter \<open>Some Isar language elements\<close>

section \<open>Type checking\<close>

text \<open>
  The ZF logic is essentially untyped, so the concept of ``type
  checking'' is performed as logical reasoning about set-membership
  statements.  A special method assists users in this task; a version
  of this is already declared as a ``solver'' in the standard
  Simplifier setup.

  \begin{matharray}{rcl}
    @{command_def (ZF) "print_tcset"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{method_def (ZF) typecheck} & : & \<open>method\<close> \\
    @{attribute_def (ZF) TC} & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{attribute (ZF) TC} (() | 'add' | 'del')
  \<close>

  \begin{description}
  
  \item @{command (ZF) "print_tcset"} prints the collection of
  typechecking rules of the current context.
  
  \item @{method (ZF) typecheck} attempts to solve any pending
  type-checking problems in subgoals.
  
  \item @{attribute (ZF) TC} adds or deletes type-checking rules from
  the context.

  \end{description}
\<close>


section \<open>(Co)Inductive sets and datatypes\<close>

subsection \<open>Set definitions\<close>

text \<open>
  In ZF everything is a set.  The generic inductive package also
  provides a specific view for ``datatype'' specifications.
  Coinductive definitions are available in both cases, too.

  \begin{matharray}{rcl}
    @{command_def (ZF) "inductive"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def (ZF) "coinductive"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def (ZF) "datatype"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{command_def (ZF) "codatatype"} & : & \<open>theory \<rightarrow> theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{command (ZF) inductive} | @@{command (ZF) coinductive}) domains intros hints
    ;

    domains: @'domains' (@{syntax term} + '+') ('<=' | '\<subseteq>') @{syntax term}
    ;
    intros: @'intros' (@{syntax thmdecl}? @{syntax prop} +)
    ;
    hints: @{syntax (ZF) "monos"}? condefs? \<newline>
      @{syntax (ZF) typeintros}? @{syntax (ZF) typeelims}?
    ;
    @{syntax_def (ZF) "monos"}: @'monos' @{syntax thms}
    ;
    condefs: @'con_defs' @{syntax thms}
    ;
    @{syntax_def (ZF) typeintros}: @'type_intros' @{syntax thms}
    ;
    @{syntax_def (ZF) typeelims}: @'type_elims' @{syntax thms}
  \<close>

  In the following syntax specification \<open>monos\<close>, \<open>typeintros\<close>, and \<open>typeelims\<close> are the same as above.

  \<^rail>\<open>
    (@@{command (ZF) datatype} | @@{command (ZF) codatatype}) domain? (dtspec + @'and') hints
    ;

    domain: ('<=' | '\<subseteq>') @{syntax term}
    ;
    dtspec: @{syntax term} '=' (con + '|')
    ;
    con: @{syntax name} ('(' (@{syntax term} ',' +) ')')?
    ;
    hints: @{syntax (ZF) "monos"}? @{syntax (ZF) typeintros}? @{syntax (ZF) typeelims}?
  \<close>

  See @{cite "isabelle-ZF"} for further information on inductive
  definitions in ZF, but note that this covers the old-style theory
  format.
\<close>


subsection \<open>Primitive recursive functions\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def (ZF) "primrec"} & : & \<open>theory \<rightarrow> theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command (ZF) primrec} (@{syntax thmdecl}? @{syntax prop} +)
  \<close>
\<close>


subsection \<open>Cases and induction: emulating tactic scripts\<close>

text \<open>
  The following important tactical tools of Isabelle/ZF have been
  ported to Isar.  These should not be used in proper proof texts.

  \begin{matharray}{rcl}
    @{method_def (ZF) case_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def (ZF) induct_tac}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def (ZF) ind_cases}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{command_def (ZF) "inductive_cases"} & : & \<open>theory \<rightarrow> theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{method (ZF) case_tac} | @@{method (ZF) induct_tac}) @{syntax goal_spec}? @{syntax name}
    ;
    @@{method (ZF) ind_cases} (@{syntax prop} +)
    ;
    @@{command (ZF) inductive_cases} (@{syntax thmdecl}? (@{syntax prop} +) + @'and')
  \<close>
\<close>

end
