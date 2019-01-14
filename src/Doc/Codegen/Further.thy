theory Further
imports Setup
begin

section \<open>Further issues \label{sec:further}\<close>

subsection \<open>Incorporating generated code directly into the system runtime -- \<open>code_reflect\<close>\<close>

subsubsection \<open>Static embedding of generated code into the system runtime\<close>

text \<open>
  The @{ML_antiquotation code} antiquotation is lightweight, but the generated code
  is only accessible while the ML section is processed.  Sometimes this
  is not appropriate, especially if the generated code contains datatype
  declarations which are shared with other parts of the system.  In these
  cases, @{command_def code_reflect} can be used:
\<close>

code_reflect %quote Sum_Type
  datatypes sum = Inl | Inr
  functions "Sum_Type.sum.projl" "Sum_Type.sum.projr"

text \<open>
  \noindent @{command code_reflect} takes a structure name and
  references to datatypes and functions; for these code is compiled
  into the named ML structure and the \emph{Eval} target is modified
  in a way that future code generation will reference these
  precompiled versions of the given datatypes and functions.  This
  also allows to refer to the referenced datatypes and functions from
  arbitrary ML code as well.

  A typical example for @{command code_reflect} can be found in the
  \<^theory>\<open>HOL.Predicate\<close> theory.
\<close>


subsubsection \<open>Separate compilation\<close>

text \<open>
  For technical reasons it is sometimes necessary to separate
  generation and compilation of code which is supposed to be used in
  the system runtime.  For this @{command code_reflect} with an
  optional \<^theory_text>\<open>file\<close> argument can be used:
\<close>

code_reflect %quote Rat
  datatypes rat
  functions Fract
    "(plus :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(minus :: rat \<Rightarrow> rat \<Rightarrow> rat)"
    "(times :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(divide :: rat \<Rightarrow> rat \<Rightarrow> rat)"
  file "$ISABELLE_TMP/rat.ML"

text \<open>
  \noindent This merely generates the referenced code to the given
  file which can be included into the system runtime later on.
\<close>

subsection \<open>Specialities of the \<open>Scala\<close> target language \label{sec:scala}\<close>

text \<open>
  \<open>Scala\<close> deviates from languages of the ML family in a couple
  of aspects; those which affect code generation mainly have to do with
  \<open>Scala\<close>'s type system:

  \begin{itemize}

    \item \<open>Scala\<close> prefers tupled syntax over curried syntax.

    \item \<open>Scala\<close> sacrifices Hindely-Milner type inference for a
      much more rich type system with subtyping etc.  For this reason
      type arguments sometimes have to be given explicitly in square
      brackets (mimicking System F syntax).

    \item In contrast to \<open>Haskell\<close> where most specialities of
      the type system are implemented using \emph{type classes},
      \<open>Scala\<close> provides a sophisticated system of \emph{implicit
      arguments}.

  \end{itemize}

  \noindent Concerning currying, the \<open>Scala\<close> serializer counts
  arguments in code equations to determine how many arguments
  shall be tupled; remaining arguments and abstractions in terms
  rather than function definitions are always curried.

  The second aspect affects user-defined adaptations with @{command
  code_printing}.  For regular terms, the \<open>Scala\<close> serializer prints
  all type arguments explicitly.  For user-defined term adaptations
  this is only possible for adaptations which take no arguments: here
  the type arguments are just appended.  Otherwise they are ignored;
  hence user-defined adaptations for polymorphic constants have to be
  designed very carefully to avoid ambiguity.

  Note also that name clashes can occur when generating Scala code
  to case-insensitive file systems; these can be avoid using the
  ``\<open>(case_insensitive)\<close>'' option for @{command export_code}.
\<close>


subsection \<open>Modules namespace\<close>

text \<open>
  When invoking the @{command export_code} command it is possible to
  leave out the @{keyword "module_name"} part; then code is
  distributed over different modules, where the module name space
  roughly is induced by the Isabelle theory name space.

  Then sometimes the awkward situation occurs that dependencies
  between definitions introduce cyclic dependencies between modules,
  which in the \<open>Haskell\<close> world leaves you to the mercy of the
  \<open>Haskell\<close> implementation you are using, while for \<open>SML\<close>/\<open>OCaml\<close> code generation is not possible.

  A solution is to declare module names explicitly.  Let use assume
  the three cyclically dependent modules are named \emph{A}, \emph{B}
  and \emph{C}.  Then, by stating
\<close>

code_identifier %quote
  code_module A \<rightharpoonup> (SML) ABC
| code_module B \<rightharpoonup> (SML) ABC
| code_module C \<rightharpoonup> (SML) ABC

text \<open>
  \noindent we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules at serialisation
  time.
\<close>

subsection \<open>Locales and interpretation\<close>

text \<open>
  A technical issue comes to surface when generating code from
  specifications stemming from locale interpretation into global
  theories.

  Let us assume a locale specifying a power operation on arbitrary
  types:
\<close>

locale %quote power =
  fixes power :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes power_commute: "power x \<circ> power y = power y \<circ> power x"
begin

text \<open>
  \noindent Inside that locale we can lift \<open>power\<close> to exponent
  lists by means of a specification relative to that locale:
\<close>

primrec %quote powers :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "powers [] = id"
| "powers (x # xs) = power x \<circ> powers xs"

lemma %quote powers_append:
  "powers (xs @ ys) = powers xs \<circ> powers ys"
  by (induct xs) simp_all

lemma %quote powers_power:
  "powers xs \<circ> power x = power x \<circ> powers xs"
  by (induct xs)
    (simp_all del: o_apply id_apply add: comp_assoc,
      simp del: o_apply add: o_assoc power_commute)

lemma %quote powers_rev:
  "powers (rev xs) = powers xs"
    by (induct xs) (simp_all add: powers_append powers_power)

end %quote

text \<open>
  After an interpretation of this locale (say, @{command_def
  global_interpretation} \<open>fun_power:\<close> @{term [source] "power (\<lambda>n (f
  :: 'a \<Rightarrow> 'a). f ^^ n)"}), one could naively expect to have a constant \<open>fun_power.powers :: nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a\<close> for which code
  can be generated.  But this not the case: internally, the term
  \<open>fun_power.powers\<close> is an abbreviation for the foundational
  term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  (see @{cite "isabelle-locale"} for the details behind).

  Fortunately, a succint solution is available: a dedicated
  rewrite definition:
\<close>

global_interpretation %quote fun_power: power "(\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"
  defines funpows = fun_power.powers
  by unfold_locales
    (simp_all add: fun_eq_iff funpow_mult mult.commute)

text \<open>
  \noindent This amends the interpretation morphisms such that
  occurrences of the foundational term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  are folded to a newly defined constant \<^const>\<open>funpows\<close>.

  After this setup procedure, code generation can continue as usual:
\<close>

text %quote \<open>
  @{code_stmts funpows (consts) Nat.funpow funpows (Haskell)}
\<close>


subsection \<open>Parallel computation\<close>

text \<open>
  Theory \<open>Parallel\<close> in \<^dir>\<open>~~/src/HOL/Library\<close> contains
  operations to exploit parallelism inside the Isabelle/ML
  runtime engine.
\<close>

subsection \<open>Imperative data structures\<close>

text \<open>
  If you consider imperative data structures as inevitable for a
  specific application, you should consider \emph{Imperative
  Functional Programming with Isabelle/HOL}
  @{cite "bulwahn-et-al:2008:imperative"}; the framework described there
  is available in session \<open>Imperative_HOL\<close>, together with a
  short primer document.
\<close>

end
