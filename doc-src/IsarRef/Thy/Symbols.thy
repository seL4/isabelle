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
  are displayed properly in Proof~General and Isabelle/jEdit.

  Moreover, any single symbol (or ASCII character) may be prefixed by
  @{verbatim "\\"}@{verbatim "<^sup>"}, for superscript and @{verbatim
  "\\"}@{verbatim "<^sub>"}, for subscript, such as @{verbatim
  "A\\"}@{verbatim "<^sup>\<star>"}, for @{text "A\<^sup>\<star>"} the alternative
  versions @{verbatim "\\"}@{verbatim "<^isub>"} and @{verbatim
  "\\"}@{verbatim "<^isup>"} are considered as quasi letters and may
  be used within identifiers.  Sub- and superscripts that span a
  region of text are marked up with @{verbatim "\\"}@{verbatim
  "<^bsub>"}@{text "\<dots>"}@{verbatim "\\"}@{verbatim "<^esub>"}, and
  @{verbatim "\\"}@{verbatim "<^bsup>"}@{text "\<dots>"}@{verbatim
  "\\"}@{verbatim "<^esup>"} respectively.  Furthermore, all ASCII
  characters and most other symbols may be printed in bold by
  prefixing @{verbatim "\\"}@{verbatim "<^bold>"} such as @{verbatim
  "\\"}@{verbatim "<^bold>\\"}@{verbatim "<alpha>"} for @{text
  "\<^bold>\<alpha>"}.  Note that @{verbatim "\\"}@{verbatim "<^bold>"}, may
  \emph{not} be combined with sub- or superscripts for single symbols.

  Further details of Isabelle document preparation are covered in
  \chref{ch:document-prep}.

  \begin{center}
  \begin{isabellebody}
  \input{syms}  
  \end{isabellebody}
  \end{center}
*}

end