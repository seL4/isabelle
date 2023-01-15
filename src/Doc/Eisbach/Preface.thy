(*:maxLineLen=78:*)

theory Preface
imports Base "HOL-Eisbach.Eisbach_Tools"
begin

text \<open>
  \<^emph>\<open>Eisbach\<close> is a collection of tools which form the basis for defining new
  proof methods in Isabelle/Isar~\<^cite>\<open>"Wenzel-PhD"\<close>. It can be thought of as
  a ``proof method language'', but is more precisely an infrastructure for
  defining new proof methods out of existing ones.

  The core functionality of Eisbach is provided by the Isar @{command method}
  command. Here users may define new methods by combining existing ones with
  the usual Isar syntax. These methods can be abstracted over terms, facts and
  other methods, as one might expect in any higher-order functional language.

  Additional functionality is provided by extending the space of methods and
  attributes. The new @{method match} method allows for explicit control-flow,
  by taking a match target and a list of pattern-method pairs. By using the
  functionality provided by Eisbach, additional support methods can be easily
  written. For example, the @{method catch} method, which provides basic
  try-catch functionality, only requires a few lines of ML.

  Eisbach enables users to implement automated proof tools conveniently via
  Isabelle/Isar syntax. This is in contrast to the traditional approach to use
  Isabelle/ML (via @{command_ref method_setup}), which poses a higher
  barrier-to-entry for casual users.

  \<^medskip>
  This manual is written for readers familiar with Isabelle/Isar, but not
  necessarily Isabelle/ML. It covers the usage of the @{command method} as
  well as the @{method match} method, as well as discussing their integration
  with existing Isar concepts such as @{command named_theorems}.

  These commands are provided by theory \<^theory>\<open>HOL-Eisbach.Eisbach\<close>: it
  needs to be imported by all Eisbach applications. Theory
  \<^theory>\<open>HOL-Eisbach.Eisbach_Tools\<close> provides additional proof methods and
  attributes that are occasionally useful.
\<close>

end
