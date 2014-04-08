theory Symbols
imports Base Main
begin

chapter {* Predefined Isabelle symbols \label{app:symbols} *}

text {*
  Isabelle supports an infinite number of non-ASCII symbols, which are
  represented in source text as @{verbatim "\\"}@{verbatim "<"}@{text
  name}@{verbatim ">"} (where @{text name} may be any identifier).  It
  is left to front-end tools how to present these symbols to the user.
  The collection of predefined standard symbols given below is
  available by default for Isabelle document output, due to
  appropriate definitions of @{verbatim "\\"}@{verbatim isasym}@{text
  name} for each @{verbatim "\\"}@{verbatim "<"}@{text name}@{verbatim
  ">"} in the @{verbatim isabellesym.sty} file.  Most of these symbols
  are displayed properly in Isabelle/jEdit and {\LaTeX} generated from Isabelle.

  Moreover, any single symbol (or ASCII character) may be prefixed by
  @{verbatim "\<^sup>"} for superscript and @{verbatim "\<^sub>"} for subscript,
  such as @{verbatim "A\<^sup>\<star>"} for @{text "A\<^sup>\<star>"} and @{verbatim "A\<^sub>1"} for
  @{text "A\<^sub>1"}.  Sub- and superscripts that span a region of text can
  be marked up with @{verbatim "\<^bsub>"}@{text "\<dots>"}@{verbatim
  "\<^esub>"} and @{verbatim "\<^bsup>"}@{text "\<dots>"}@{verbatim "\<^esup>"}
  respectively, but note that there are limitations in the typographic
  rendering quality of this form.  Furthermore, all ASCII characters
  and most other symbols may be printed in bold by prefixing
  @{verbatim "\<^bold>"} such as @{verbatim "\<^bold>\<alpha>"} for @{text "\<^bold>\<alpha>"}.  Note that
  @{verbatim "\<^sup>"}, @{verbatim "\<^sub>"}, @{verbatim "\<^bold>"} cannot be combined.

  Further details of Isabelle document preparation are covered in
  \chref{ch:document-prep}.

  \begin{center}
  \begin{isabellebody}
  \input{syms}  
  \end{isabellebody}
  \end{center}
*}

end