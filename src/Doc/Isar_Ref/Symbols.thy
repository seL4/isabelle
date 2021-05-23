(*:maxLineLen=78:*)

theory Symbols
  imports Main Base
begin

chapter \<open>Predefined Isabelle symbols \label{app:symbols}\<close>

text \<open>
  Isabelle supports an infinite number of non-ASCII symbols, which are
  represented in source text as \<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>name\<close>\<^verbatim>\<open>>\<close> (where \<open>name\<close> may be any identifier).  It
  is left to front-end tools how to present these symbols to the user.
  The collection of predefined standard symbols given below is
  available by default for Isabelle document output, due to
  appropriate definitions of \<^verbatim>\<open>\isasym\<close>\<open>name\<close> for each \<^verbatim>\<open>\\<close>\<^verbatim>\<open><\<close>\<open>name\<close>\<^verbatim>\<open>>\<close> in
  the \<^verbatim>\<open>isabellesym.sty\<close> file.  Most of these symbols
  are displayed properly in Isabelle/jEdit and {\LaTeX} generated from Isabelle.

  Moreover, any single symbol (or ASCII character) may be prefixed by
  \<^verbatim>\<open>\<^sup>\<close> for superscript and \<^verbatim>\<open>\<^sub>\<close> for subscript,
  such as \<^verbatim>\<open>A\<^sup>\<star>\<close> for \<open>A\<^sup>\<star>\<close> and \<^verbatim>\<open>A\<^sub>1\<close> for
  \<open>A\<^sub>1\<close>.  Sub- and superscripts that span a region of text can
  be marked up with \<^verbatim>\<open>\<^bsub>\<close>\<open>\<dots>\<close>\<^verbatim>\<open>\<^esub>\<close> and \<^verbatim>\<open>\<^bsup>\<close>\<open>\<dots>\<close>\<^verbatim>\<open>\<^esup>\<close>
  respectively, but note that there are limitations in the typographic
  rendering quality of this form.  Furthermore, all ASCII characters
  and most other symbols may be printed in bold by prefixing
  \<^verbatim>\<open>\<^bold>\<close> such as \<^verbatim>\<open>\<^bold>\<alpha>\<close> for \<open>\<^bold>\<alpha>\<close>.  Note that
  \<^verbatim>\<open>\<^sup>\<close>, \<^verbatim>\<open>\<^sub>\<close>, \<^verbatim>\<open>\<^bold>\<close> cannot be combined.

  Further details of Isabelle document preparation are covered in
  \chref{ch:document-prep}.

  \begin{center}
  \begin{isabellebody}
  @{show_symbols}
  \end{isabellebody}
  \end{center}
\<close>

end
