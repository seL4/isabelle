(* $Id$ *)

theory Misc
imports Main
begin

chapter {* Other commands \label{ch:pure-syntax} *}

section {* Diagnostics *}

text {*
  \begin{matharray}{rcl}
    @{command_def "pr"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "thm"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "term"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "prop"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "typ"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "prf"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "full_prf"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
  \end{matharray}

  These diagnostic commands assist interactive development.  Note that
  @{command undo} does not apply here, the theory or proof
  configuration is not changed.

  \begin{rail}
    'pr' modes? nat? (',' nat)?
    ;
    'thm' modes? thmrefs
    ;
    'term' modes? term
    ;
    'prop' modes? prop
    ;
    'typ' modes? type
    ;
    'prf' modes? thmrefs?
    ;
    'full\_prf' modes? thmrefs?
    ;

    modes: '(' (name + ) ')'
    ;
  \end{rail}

  \begin{description}

  \item @{command "pr"}~@{text "goals, prems"} prints the current
  proof state (if present), including the proof context, current facts
  and goals.  The optional limit arguments affect the number of goals
  and premises to be displayed, which is initially 10 for both.
  Omitting limit values leaves the current setting unchanged.

  \item @{command "thm"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"} retrieves
  theorems from the current theory or proof context.  Note that any
  attributes included in the theorem specifications are applied to a
  temporary context derived from the current theory or proof; the
  result is discarded, i.e.\ attributes involved in @{text "a\<^sub>1,
  \<dots>, a\<^sub>n"} do not have any permanent effect.

  \item @{command "term"}~@{text t} and @{command "prop"}~@{text \<phi>}
  read, type-check and print terms or propositions according to the
  current theory or proof context; the inferred type of @{text t} is
  output as well.  Note that these commands are also useful in
  inspecting the current environment of term abbreviations.

  \item @{command "typ"}~@{text \<tau>} reads and prints types of the
  meta-logic according to the current theory or proof context.

  \item @{command "prf"} displays the (compact) proof term of the
  current proof state (if present), or of the given theorems. Note
  that this requires proof terms to be switched on for the current
  object logic (see the ``Proof terms'' section of the Isabelle
  reference manual for information on how to do this).

  \item @{command "full_prf"} is like @{command "prf"}, but displays
  the full proof term, i.e.\ also displays information omitted in the
  compact proof term, which is denoted by ``@{text _}'' placeholders
  there.

  \end{description}

  All of the diagnostic commands above admit a list of @{text modes}
  to be specified, which is appended to the current print mode (see
  also \cite{isabelle-ref}).  Thus the output behavior may be modified
  according particular print mode features.  For example, @{command
  "pr"}~@{text "(latex xsymbols symbols)"} would print the current
  proof state with mathematical symbols and special characters
  represented in {\LaTeX} source, according to the Isabelle style
  \cite{isabelle-sys}.

  Note that antiquotations (cf.\ \secref{sec:antiq}) provide a more
  systematic way to include formal items into the printed text
  document.
*}


section {* Inspecting the context *}

text {*
  \begin{matharray}{rcl}
    @{command_def "print_commands"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "print_theory"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_syntax"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_methods"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_attributes"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_theorems"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "find_theorems"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "thm_deps"}@{text "\<^sup>*"} & : & \isarkeep{theory~|~proof} \\
    @{command_def "print_facts"}@{text "\<^sup>*"} & : & \isarkeep{proof} \\
    @{command_def "print_binds"}@{text "\<^sup>*"} & : & \isarkeep{proof} \\
  \end{matharray}

  \begin{rail}
    'print\_theory' ( '!'?)
    ;

    'find\_theorems' (('(' (nat)? ('with\_dups')? ')')?) (criterion *)
    ;
    criterion: ('-'?) ('name' ':' nameref | 'intro' | 'elim' | 'dest' |
      'simp' ':' term | term)
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

  \item @{command "print_syntax"} prints the inner syntax of types
  and terms, depending on the current context.  The output can be very
  verbose, including grammar tables and syntax translation rules.  See
  \cite[\S7, \S8]{isabelle-ref} for further information on Isabelle's
  inner syntax.
  
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
  respectively.  The criterion @{text "simp: t"} selects all rewrite
  rules whose left-hand side matches the given term.  The criterion
  term @{text t} selects all theorems that contain the pattern @{text
  t} -- as usual, patterns may contain occurrences of the dummy
  ``@{text _}'', schematic variables, and type constraints.
  
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
    @{command_def "undo"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
    @{command_def "linear_undo"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
    @{command_def "kill"}^{{ * }{ * }} & : & \isarkeep{\cdot} \\
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
    @{command_def "cd"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "pwd"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
    @{command_def "use_thy"}@{text "\<^sup>*"} & : & \isarkeep{\cdot} \\
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
