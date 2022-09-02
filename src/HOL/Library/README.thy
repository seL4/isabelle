theory README imports Main
begin

section \<open>HOL-Library: supplemental theories for main Isabelle/HOL\<close>

text \<open>
  This is a collection of generic theories that may be used together with main
  Isabelle/HOL.

  Addition of new theories should be done with some care, as the ``module
  system'' of Isabelle is rather simplistic. The following guidelines may be
  helpful to achieve maximum re-usability and minimum clashes with existing
  developments.

  \<^descr>[Examples] Theories should be as ``generic'' as is sensible. Unused (or
  rather unusable?) theories should be avoided; common applications should
  actually refer to the present theory. Small example uses may be included in
  the library as well, but should be put in a separate theory, such as
  \<^verbatim>\<open>Foobar.thy\<close> accompanied by \<^verbatim>\<open>Foobar_Examples.thy\<close>.

  \<^descr>[Names of logical items] There are separate hierarchically structured name
  spaces for types, constants, theorems etc. Nevertheless, some care should be
  taken, as the name spaces are always ``open''. Use adequate names; avoid
  unreadable abbreviations. The general naming convention is to separate word
  constituents by underscores, as in \<^verbatim>\<open>foo_bar\<close> or \<^verbatim>\<open>Foo_Bar\<close> (this looks best
  in LaTeX output).

  \<^descr>[Global context declarations] Only items introduced in the present theory
  should be declared globally (e.g. as Simplifier rules). Note that adding and
  deleting rules from parent theories may result in strange behavior later,
  depending on the user's arrangement of import lists.

  \<^descr>[Spacing] Isabelle is able to produce a high-quality LaTeX document from
  the theory sources, provided some minor issues are taken care of. In
  particular, spacing and line breaks are directly taken from source text.
  Incidentally, output looks very good if common type-setting conventions are
  observed: put a single space \<^emph>\<open>after\<close> each punctuation character ("\<^verbatim>\<open>,\<close>",
  "\<^verbatim>\<open>.\<close>", etc.), but none before it; do not extra spaces inside of
  parentheses; do not attempt to simulate table markup with spaces, avoid
  ``hanging'' indentations.
\<close>

end
