theory Misc
imports Base Main
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
    @{command_def "find_consts"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "thm_deps"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "unused_thms"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_facts"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
    @{command_def "print_binds"}@{text "\<^sup>*"} & : & @{text "context \<rightarrow>"} \\
  \end{matharray}

  @{rail "
    (@@{command print_theory} | @@{command print_theorems}) ('!'?)
    ;

    @@{command find_theorems} ('(' @{syntax nat}? 'with_dups'? ')')? \\ (thmcriterion * )
    ;
    thmcriterion: ('-'?) ('name' ':' @{syntax nameref} | 'intro' | 'elim' | 'dest' |
      'solves' | 'simp' ':' @{syntax term} | @{syntax term})
    ;
    @@{command find_consts} (constcriterion * )
    ;
    constcriterion: ('-'?)
      ('name' ':' @{syntax nameref} | 'strict' ':' @{syntax type} | @{syntax type})
    ;
    @@{command thm_deps} @{syntax thmrefs}
    ;
    @@{command unused_thms} ((@{syntax name} +) '-' (@{syntax name} * ))?
  "}

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
  
  \item @{command "print_theorems"} prints theorems resulting from the
  last command; the ``@{text "!"}'' option indicates extra verbosity.
  
  \item @{command "find_theorems"}~@{text criteria} retrieves facts
  from the theory or proof context matching all of given search
  criteria.  The criterion @{text "name: p"} selects all theorems
  whose fully qualified name matches pattern @{text p}, which may
  contain ``@{text "*"}'' wildcards.  The criteria @{text intro},
  @{text elim}, and @{text dest} select theorems that match the
  current goal as introduction, elimination or destruction rules,
  respectively.  The criterion @{text "solves"} returns all rules
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

  \item @{command "find_consts"}~@{text criteria} prints all constants
  whose type meets all of the given criteria. The criterion @{text
  "strict: ty"} is met by any type that matches the type pattern
  @{text ty}.  Patterns may contain both the dummy type ``@{text _}''
  and sort constraints. The criterion @{text ty} is similar, but it
  also matches against subtypes. The criterion @{text "name: p"} and
  the prefix ``@{text "-"}'' function as described for @{command
  "find_theorems"}.

  \item @{command "thm_deps"}~@{text "a\<^sub>1 \<dots> a\<^sub>n"}
  visualizes dependencies of facts, using Isabelle's graph browser
  tool (see also \cite{isabelle-sys}).

  \item @{command "unused_thms"}~@{text "A\<^isub>1 \<dots> A\<^isub>m - B\<^isub>1 \<dots> B\<^isub>n"}
  displays all unused theorems in theories @{text "B\<^isub>1 \<dots> B\<^isub>n"}
  or their parents, but not in @{text "A\<^isub>1 \<dots> A\<^isub>m"} or their parents.
  If @{text n} is @{text 0}, the end of the range of theories
  defaults to the current theory. If no range is specified,
  only the unused theorems in the current theory are displayed.
  
  \item @{command "print_facts"} prints all local facts of the
  current context, both named and unnamed ones.
  
  \item @{command "print_binds"} prints all term abbreviations
  present in the context.

  \end{description}
*}


section {* System commands *}

text {*
  \begin{matharray}{rcl}
    @{command_def "cd"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "pwd"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
    @{command_def "use_thy"}@{text "\<^sup>*"} & : & @{text "any \<rightarrow>"} \\
  \end{matharray}

  @{rail "
    (@@{command cd} | @@{command use_thy}) @{syntax name}
  "}

  \begin{description}

  \item @{command "cd"}~@{text path} changes the current directory
  of the Isabelle process.

  \item @{command "pwd"} prints the current working directory.

  \item @{command "use_thy"}~@{text A} preload theory @{text A}.
  These system commands are scarcely used when working interactively,
  since loading of theories is done automatically as required.

  \end{description}

  %FIXME proper place (!?)
  Isabelle file specification may contain path variables (e.g.\
  @{verbatim "$ISABELLE_HOME"}) that are expanded accordingly.  Note
  that @{verbatim "~"} abbreviates @{verbatim "$USER_HOME"}, and
  @{verbatim "~~"} abbreviates @{verbatim "$ISABELLE_HOME"}.  The
  general syntax for path specifications follows POSIX conventions.
*}

end
