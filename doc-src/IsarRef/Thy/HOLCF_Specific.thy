theory HOLCF_Specific
imports HOLCF
begin

chapter {* Isabelle/HOLCF \label{ch:holcf} *}

section {* Mixfix syntax for continuous operations *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOLCF) "consts"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  HOLCF provides a separate type for continuous functions @{text "\<alpha> \<rightarrow>
  \<beta>"}, with an explicit application operator @{term "f \<cdot> x"}.
  Isabelle mixfix syntax normally refers directly to the pure
  meta-level function type @{text "\<alpha> \<Rightarrow> \<beta>"}, with application @{text "f
  x"}.

  The HOLCF variant of @{command (HOLCF) "consts"} modifies that of
  Pure Isabelle (cf.\ \secref{sec:consts}) such that declarations
  involving continuous function types are treated specifically.  Any
  given syntax template is transformed internally, generating
  translation rules for the abstract and concrete representation of
  continuous application.  Note that mixing of HOLCF and Pure
  application is \emph{not} supported!
*}


section {* Recursive domains *}

text {*
  \begin{matharray}{rcl}
    @{command_def (HOLCF) "domain"} & : & @{text "theory \<rightarrow> theory"} \\
  \end{matharray}

  \begin{rail}
    'domain' parname? (dmspec + 'and')
    ;

    dmspec: typespec '=' (cons + '|')
    ;
    cons: name (type *) mixfix?
    ;
    dtrules: 'distinct' thmrefs 'inject' thmrefs 'induction' thmrefs
  \end{rail}

  Recursive domains in HOLCF are analogous to datatypes in classical
  HOL (cf.\ \secref{sec:hol-datatype}).  Mutual recursion is
  supported, but no nesting nor arbitrary branching.  Domain
  constructors may be strict (default) or lazy, the latter admits to
  introduce infinitary objects in the typical LCF manner (e.g.\ lazy
  lists).  See also \cite{MuellerNvOS99} for a general discussion of
  HOLCF domains.
*}

end
