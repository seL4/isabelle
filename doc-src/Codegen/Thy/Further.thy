theory Further
imports Setup
begin

section {* Further issues \label{sec:further} *}

subsection {* Specialities of the @{text Scala} target language \label{sec:scala} *}

text {*
  @{text Scala} deviates from languages of the ML family in a couple
  of aspects; those which affect code generation mainly have to do with
  @{text Scala}'s type system:

  \begin{itemize}

    \item @{text Scala} prefers tupled syntax over curried syntax.

    \item @{text Scala} sacrifices Hindely-Milner type inference for a
      much more rich type system with subtyping etc.  For this reason
      type arguments sometimes have to be given explicitly in square
      brackets (mimicing System F syntax).

    \item In contrast to @{text Haskell} where most specialities of
      the type system are implemented using \emph{type classes},
      @{text Scala} provides a sophisticated system of \emph{implicit
      arguments}.

  \end{itemize}

  \noindent Concerning currying, the @{text Scala} serializer counts
  arguments in code equations to determine how many arguments
  shall be tupled; remaining arguments and abstractions in terms
  rather than function definitions are always curried.

  The second aspect affects user-defined adaptations with @{command
  code_const}.  For regular terms, the @{text Scala} serializer prints
  all type arguments explicitly.  For user-defined term adaptations
  this is only possible for adaptations which take no arguments: here
  the type arguments are just appended.  Otherwise they are ignored;
  hence user-defined adaptations for polymorphic constants have to be
  designed very carefully to avoid ambiguity.

  Isabelle's type classes are mapped onto @{text Scala} implicits; in
  cases with diamonds in the subclass hierarchy this can lead to
  ambiguities in the generated code:
*}

class %quote class1 =
  fixes foo :: "'a \<Rightarrow> 'a"

class %quote class2 = class1

class %quote class3 = class1

text {*
  \noindent Here both @{class class2} and @{class class3} inherit from @{class class1},
  forming the upper part of a diamond.
*}

definition %quote bar :: "'a :: {class2, class3} \<Rightarrow> 'a" where
  "bar = foo"

text {*
  \noindent This yields the following code:
*}

text %quotetypewriter {*
  @{code_stmts bar (Scala)}
*}

text {*
  \noindent This code is rejected by the @{text Scala} compiler: in
  the definition of @{text bar}, it is not clear from where to derive
  the implicit argument for @{text foo}.

  The solution to the problem is to close the diamond by a further
  class with inherits from both @{class class2} and @{class class3}:
*}

class %quote class4 = class2 + class3

text {*
  \noindent Then the offending code equation can be restricted to
  @{class class4}:
*}

lemma %quote [code]:
  "(bar :: 'a::class4 \<Rightarrow> 'a) = foo"
  by (simp only: bar_def)

text {*
  \noindent with the following code:
*}

text %quotetypewriter {*
  @{code_stmts bar (Scala)}
*}

text {*
  \noindent which exposes no ambiguity.

  Since the preprocessor (cf.~\secref{sec:preproc}) propagates sort
  constraints through a system of code equations, it is usually not
  very difficult to identify the set of code equations which actually
  needs more restricted sort constraints.
*}

subsection {* Modules namespace *}

text {*
  When invoking the @{command export_code} command it is possible to
  leave out the @{keyword "module_name"} part; then code is
  distributed over different modules, where the module name space
  roughly is induced by the Isabelle theory name space.

  Then sometimes the awkward situation occurs that dependencies
  between definitions introduce cyclic dependencies between modules,
  which in the @{text Haskell} world leaves you to the mercy of the
  @{text Haskell} implementation you are using, while for @{text
  SML}/@{text OCaml} code generation is not possible.

  A solution is to declare module names explicitly.  Let use assume
  the three cyclically dependent modules are named \emph{A}, \emph{B}
  and \emph{C}.  Then, by stating
*}

code_modulename %quote SML
  A ABC
  B ABC
  C ABC

text {*
  \noindent we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules at serialisation
  time.
*}

subsection {* Locales and interpretation *}

text {*
  A technical issue comes to surface when generating code from
  specifications stemming from locale interpretation.

  Let us assume a locale specifying a power operation on arbitrary
  types:
*}

locale %quote power =
  fixes power :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes power_commute: "power x \<circ> power y = power y \<circ> power x"
begin

text {*
  \noindent Inside that locale we can lift @{text power} to exponent
  lists by means of specification relative to that locale:
*}

primrec %quote powers :: "'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "powers [] = id"
| "powers (x # xs) = power x \<circ> powers xs"

lemma %quote powers_append:
  "powers (xs @ ys) = powers xs \<circ> powers ys"
  by (induct xs) simp_all

lemma %quote powers_power:
  "powers xs \<circ> power x = power x \<circ> powers xs"
  by (induct xs)
    (simp_all del: o_apply id_apply add: o_assoc [symmetric],
      simp del: o_apply add: o_assoc power_commute)

lemma %quote powers_rev:
  "powers (rev xs) = powers xs"
    by (induct xs) (simp_all add: powers_append powers_power)

end %quote

text {*
  After an interpretation of this locale (say, @{command_def
  interpretation} @{text "fun_power:"} @{term [source] "power (\<lambda>n (f
  :: 'a \<Rightarrow> 'a). f ^^ n)"}), one would expect to have a constant @{text
  "fun_power.powers :: nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"} for which code
  can be generated.  But this not the case: internally, the term
  @{text "fun_power.powers"} is an abbreviation for the foundational
  term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  (see \cite{isabelle-locale} for the details behind).

  Fortunately, with minor effort the desired behaviour can be
  achieved.  First, a dedicated definition of the constant on which
  the local @{text "powers"} after interpretation is supposed to be
  mapped on:
*}

definition %quote funpows :: "nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code del]: "funpows = power.powers (\<lambda>n f. f ^^ n)"

text {*
  \noindent In general, the pattern is @{text "c = t"} where @{text c}
  is the name of the future constant and @{text t} the foundational
  term corresponding to the local constant after interpretation.

  The interpretation itself is enriched with an equation @{text "t = c"}:
*}

interpretation %quote fun_power: power "\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n" where
  "power.powers (\<lambda>n f. f ^^ n) = funpows"
  by unfold_locales
    (simp_all add: fun_eq_iff funpow_mult mult_commute funpows_def)

text {*
  \noindent This additional equation is trivially proved by the
  definition itself.

  After this setup procedure, code generation can continue as usual:
*}

text %quotetypewriter {*
  @{code_stmts funpows (consts) Nat.funpow funpows (Haskell)}
*}


subsection {* Imperative data structures *}

text {*
  If you consider imperative data structures as inevitable for a
  specific application, you should consider \emph{Imperative
  Functional Programming with Isabelle/HOL}
  \cite{bulwahn-et-al:2008:imperative}; the framework described there
  is available in session @{text Imperative_HOL}, together with a
  short primer document.
*}


subsection {* ML system interfaces \label{sec:ml} *}

text {*
  Since the code generator framework not only aims to provide a nice
  Isar interface but also to form a base for code-generation-based
  applications, here a short description of the most fundamental ML
  interfaces.
*}

subsubsection {* Managing executable content *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Code.read_const: "theory -> string -> string"} \\
  @{index_ML Code.add_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code.del_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_pre: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_post: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.add_functrans: "
    string * (theory -> (thm * bool) list -> (thm * bool) list option)
      -> theory -> theory"} \\
  @{index_ML Code_Preproc.del_functrans: "string -> theory -> theory"} \\
  @{index_ML Code.add_datatype: "(string * typ) list -> theory -> theory"} \\
  @{index_ML Code.get_type: "theory -> string
    -> ((string * sort) list * (string * ((string * sort) list * typ list)) list) * bool"} \\
  @{index_ML Code.get_type_of_constr_or_abstr: "theory -> string -> (string * bool) option"}
  \end{mldecls}

  \begin{description}

  \item @{ML Code.read_const}~@{text thy}~@{text s}
     reads a constant as a concrete term expression @{text s}.

  \item @{ML Code.add_eqn}~@{text "thm"}~@{text "thy"} adds function
     theorem @{text "thm"} to executable content.

  \item @{ML Code.del_eqn}~@{text "thm"}~@{text "thy"} removes function
     theorem @{text "thm"} from executable content, if present.

  \item @{ML Code_Preproc.map_pre}~@{text "f"}~@{text "thy"} changes
     the preprocessor simpset.

  \item @{ML Code_Preproc.add_functrans}~@{text "(name, f)"}~@{text "thy"} adds
     function transformer @{text f} (named @{text name}) to executable content;
     @{text f} is a transformer of the code equations belonging
     to a certain function definition, depending on the
     current theory context.  Returning @{text NONE} indicates that no
     transformation took place;  otherwise, the whole process will be iterated
     with the new code equations.

  \item @{ML Code_Preproc.del_functrans}~@{text "name"}~@{text "thy"} removes
     function transformer named @{text name} from executable content.

  \item @{ML Code.add_datatype}~@{text cs}~@{text thy} adds
     a datatype to executable content, with generation
     set @{text cs}.

  \item @{ML Code.get_type_of_constr_or_abstr}~@{text "thy"}~@{text "const"}
     returns type constructor corresponding to
     constructor @{text const}; returns @{text NONE}
     if @{text const} is no constructor.

  \end{description}
*}


subsubsection {* Data depending on the theory's executable content *}

text {*
  Implementing code generator applications on top of the framework set
  out so far usually not only involves using those primitive
  interfaces but also storing code-dependent data and various other
  things.

  Due to incrementality of code generation, changes in the theory's
  executable content have to be propagated in a certain fashion.
  Additionally, such changes may occur not only during theory
  extension but also during theory merge, which is a little bit nasty
  from an implementation point of view.  The framework provides a
  solution to this technical challenge by providing a functorial data
  slot @{ML_functor Code_Data}; on instantiation of this functor, the
  following types and operations are required:

  \medskip
  \begin{tabular}{l}
  @{text "type T"} \\
  @{text "val empty: T"} \\
  \end{tabular}

  \begin{description}

  \item @{text T} the type of data to store.

  \item @{text empty} initial (empty) data.

  \end{description}

  \noindent An instance of @{ML_functor Code_Data} provides the
  following interface:

  \medskip
  \begin{tabular}{l}
  @{text "change: theory \<rightarrow> (T \<rightarrow> T) \<rightarrow> T"} \\
  @{text "change_yield: theory \<rightarrow> (T \<rightarrow> 'a * T) \<rightarrow> 'a * T"}
  \end{tabular}

  \begin{description}

  \item @{text change} update of current data (cached!) by giving a
    continuation.

  \item @{text change_yield} update with side result.

  \end{description}
*}

end

