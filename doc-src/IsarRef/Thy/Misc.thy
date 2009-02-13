(* $Id$ *)

theory Misc
imports Main
begin

chapter {* Other commands *}

section {* Inspecting the context *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_commands"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "print_theory"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_methods"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_attributes"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_theorems"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "find_theorems"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "thm_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_facts"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_binds"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  \begin{rail}
    'print\_theory' ( '!'?)
    ;

    'find\_theorems' (('(' (nat)? ('with\_dups')? ')')?) (criterion *)
    ;
    criterion: ('-'?) ('name' ':' nameref | 'intro' | 'elim' | 'dest' |
      'solves' | 'simp' ':' term | term)
    ;
    'thm\_deps' thmrefs
    ;
  \end{rail}

  These commands print certain parts of the theory and proof context.
  Note that there are some further ones available, such as for the set
  of rules declared for simplifications.

  \begin{description}
  
  \item @{command "print_commands"} prints Isabelle's outer theory
  syntax, including keywords and command.
  
  \item @{command "print_theory"} prints the main logical content of
  the theory context; the ``@{text "!"}'' option indicates extra
  verbosity.

  \item @{command "print_methods"} prints all proof methods
  available in the current theory context.
  
  \item @{command "print_attributes"} prints all attributes
  available in the current theory context.
  
  \item @{command "print_theorems"} prints theorems resulting from
  the last command.
  
  \item @{command "find_theorems"}~@{text criteria} retrieves facts
  from the theory or proof context matching all of given search
  criteria.  The criterion @{text "name: p"} selects all theorems
  whose fully qualified name matches pattern @{text p}, which may
  contain ``@{text "*"}'' wildcards.  The criteria @{text intro},
  @{text elim}, and @{text dest} select theorems that match the
  current goal as introduction, elimination or destruction rules,
  respectively.  The criteria @{text "solves"} returns all rules
  that would directly solve the current goal.  The criterion
  @{text "simp: t"} selects all rewrite rules whose left-hand side
  matches the given term.  The criterion term @{text t} selects all
  theorems that contain the pattern @{text t} -- as usual, patterns
  may contain occurrences of the dummy ``@{text _}'', schematic
  variables, and type constraints.
  
  Criteria can be preceded by ``@{text "-"}'' to select theorems that
  do \emph{not} match. Note that giving the empty list of criteria
  yields \emph{all} currently known facts.  An optional limit for the
  number of printed facts may be given; the default is 40.  By
  default, duplicates are removed from the search result. Use
  @{text with_dups} to display duplicates.
  
  \item @{command "thm_deps"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}
  visualizes dependencies of facts, using Isabelle's graph browser
  tool (see also \cite{isabelle-sys}).
  
  \item @{command "print_facts"} prints all local facts of the
  current context, both named and unnamed ones.
  
  \item @{command "print_binds"} prints all term abbreviations
  present in the context.

  \end{description}
*}


section {* History commands \label{sec:history} *}

text {*
  \begin{matharray}{rcl}
    @{command_def "undo"}^{{ * }{ * }} & : & @{text "any \<rightarrow> any"} \\
    @{command_def "linear_undo"}^{{ * }{ * }} & : & @{text "any \<rightarrow> any"} \\
    @{command_def "kill"}^{{ * }{ * }} & : & @{text "any \<rightarrow> any"} \\
  \end{matharray}

  The Isabelle/Isar top-level maintains a two-stage history, for
  theory and proof state transformation.  Basically, any command can
  be undone using @{command "undo"}, excluding mere diagnostic
  elements.  Note that a theorem statement with a \emph{finished}
  proof is treated as a single unit by @{command "undo"}.  In
  contrast, the variant @{command "linear_undo"} admits to step back
  into the middle of a proof.  The @{command "kill"} command aborts
  the current history node altogether, discontinuing a proof or even
  the whole theory.  This operation is \emph{not} undo-able.

  \begin{warn}
    History commands should never be used with user interfaces such as
    Proof~General \cite{proofgeneral,Aspinall:TACAS:2000}, which takes
    care of stepping forth and back itself.  Interfering by manual
    @{command "undo"}, @{command "linear_undo"}, or even @{command
    "kill"} commands would quickly result in utter confusion.
  \end{warn}
*}


section {* System commands *}

text {*
  \begin{matharray}{rcl}
    @{command_def "cd"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "pwd"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "use_thy"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
  \end{matharray}

  \begin{rail}
    ('cd' | 'use\_thy' | 'update\_thy') name
    ;
  \end{rail}

  \begin{description}

  \item @{command "cd"}~@{text path} changes the current directory
  of the Isabelle process.

  \item @{command "pwd"} prints the current working directory.

  \item @{command "use_thy"}~@{text A} preload theory @{text A}.
  These system commands are scarcely used when working interactively,
  since loading of theories is done automatically as required.

  \end{description}
*}

end
