theory Syntax
imports Base
begin

chapter {* Concrete syntax and type-checking *}

text FIXME

section {* Reading and pretty printing \label{sec:read-print} *}

text FIXME

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.read_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.read_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.read_prop: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.pretty_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.pretty_term: "Proof.context -> term -> Pretty.T"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Parsing and unparsing \label{sec:parse-unparse} *}

text FIXME

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.parse_typ: "Proof.context -> string -> typ"} \\
  @{index_ML Syntax.parse_term: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.parse_prop: "Proof.context -> string -> term"} \\
  @{index_ML Syntax.unparse_typ: "Proof.context -> typ -> Pretty.T"} \\
  @{index_ML Syntax.unparse_term: "Proof.context -> term -> Pretty.T"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Checking and unchecking \label{sec:term-check} *}

text FIXME

text %mlref {*
  \begin{mldecls}
  @{index_ML Syntax.check_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.check_terms: "Proof.context -> term list -> term list"} \\
  @{index_ML Syntax.check_props: "Proof.context -> term list -> term list"} \\
  @{index_ML Syntax.uncheck_typs: "Proof.context -> typ list -> typ list"} \\
  @{index_ML Syntax.uncheck_terms: "Proof.context -> term list -> term list"} \\
  \end{mldecls}

  \begin{description}

  \item FIXME

  \end{description}
*}


section {* Syntax translations *}

text FIXME

text %mlantiq {*
  \begin{matharray}{rcl}
  @{ML_antiquotation_def "class_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "type_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "const_syntax"} & : & @{text ML_antiquotation} \\
  @{ML_antiquotation_def "syntax_const"} & : & @{text ML_antiquotation} \\
  \end{matharray}

  @{rail "
  (@@{ML_antiquotation class_syntax} |
   @@{ML_antiquotation type_syntax} |
   @@{ML_antiquotation const_syntax} |
   @@{ML_antiquotation syntax_const}) name
  "}

  \begin{description}

  \item FIXME

  \end{description}
*}

end
