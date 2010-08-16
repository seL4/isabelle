theory Further
imports Setup
begin

section {* Further issues \label{sec:further} *}

subsection {* Modules namespace *}

text {*
  When invoking the @{command export_code} command it is possible to leave
  out the @{keyword "module_name"} part;  then code is distributed over
  different modules, where the module name space roughly is induced
  by the Isabelle theory name space.

  Then sometimes the awkward situation occurs that dependencies between
  definitions introduce cyclic dependencies between modules, which in the
  @{text Haskell} world leaves you to the mercy of the @{text Haskell} implementation
  you are using,  while for @{text SML}/@{text OCaml} code generation is not possible.

  A solution is to declare module names explicitly.
  Let use assume the three cyclically dependent
  modules are named \emph{A}, \emph{B} and \emph{C}.
  Then, by stating
*}

code_modulename %quote SML
  A ABC
  B ABC
  C ABC

text {*\noindent
  we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules
  at serialisation time.
*}

subsection {* Locales and interpretation *}

text {*
  A technical issue comes to surface when generating code from
  specifications stemming from locale interpretation.

  Let us assume a locale specifying a power operation
  on arbitrary types:
*}

locale %quote power =
  fixes power :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes power_commute: "power x \<circ> power y = power y \<circ> power x"
begin

text {*
  \noindent Inside that locale we can lift @{text power} to exponent lists
  by means of specification relative to that locale:
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
  After an interpretation of this locale (say, @{command
  interpretation} @{text "fun_power:"} @{term [source] "power (\<lambda>n (f ::
  'a \<Rightarrow> 'a). f ^^ n)"}), one would expect to have a constant @{text
  "fun_power.powers :: nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"} for which code
  can be generated.  But this not the case: internally, the term
  @{text "fun_power.powers"} is an abbreviation for the foundational
  term @{term [source] "power.powers (\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n)"}
  (see \cite{isabelle-locale} for the details behind).

  Fortunately, with minor effort the desired behaviour can be achieved.
  First, a dedicated definition of the constant on which the local @{text "powers"}
  after interpretation is supposed to be mapped on:
*}

definition %quote funpows :: "nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code del]: "funpows = power.powers (\<lambda>n f. f ^^ n)"

text {*
  \noindent In general, the pattern is @{text "c = t"} where @{text c} is
  the name of the future constant and @{text t} the foundational term
  corresponding to the local constant after interpretation.

  The interpretation itself is enriched with an equation @{text "t = c"}:
*}

interpretation %quote fun_power: power "\<lambda>n (f :: 'a \<Rightarrow> 'a). f ^^ n" where
  "power.powers (\<lambda>n f. f ^^ n) = funpows"
  by unfold_locales
    (simp_all add: expand_fun_eq funpow_mult mult_commute funpows_def)

text {*
  \noindent This additional equation is trivially proved by the definition
  itself.

  After this setup procedure, code generation can continue as usual:
*}

text %quote {*@{code_stmts funpows (consts) Nat.funpow funpows (Haskell)}*}


subsection {* Imperative data structures *}

text {*
  If you consider imperative data structures as inevitable for a
  specific application, you should consider \emph{Imperative
  Functional Programming with Isabelle/HOL}
  \cite{bulwahn-et-al:2008:imperative}; the framework described there
  is available in session @{theory Imperative_HOL}.
*}


subsection {* Evaluation oracle *}

text {*
  Code generation may also be used to \emph{evaluate} expressions
  (using @{text SML} as target language of course).
  For instance, the @{command value} reduces an expression to a
  normal form with respect to the underlying code equations:
*}

value %quote "42 / (12 :: rat)"

text {*
  \noindent will display @{term "7 / (2 :: rat)"}.

  The @{method eval} method tries to reduce a goal by code generation to @{term True}
  and solves it in that case, but fails otherwise:
*}

lemma %quote "42 / (12 :: rat) = 7 / 2"
  by %quote eval

text {*
  \noindent The soundness of the @{method eval} method depends crucially 
  on the correctness of the code generator;  this is one of the reasons
  why you should not use adaptation (see \secref{sec:adaptation}) frivolously.
*}


subsection {* Building evaluators *}

text {*
  FIXME
*}

subsubsection {* Code antiquotation *}

text {*
  In scenarios involving techniques like reflection it is quite common
  that code generated from a theory forms the basis for implementing
  a proof procedure in @{text SML}.  To facilitate interfacing of generated code
  with system code, the code generator provides a @{text code} antiquotation:
*}

datatype %quote form = T | F | And form form | Or form form (*<*)

(*>*) ML %quotett {*
  fun eval_form @{code T} = true
    | eval_form @{code F} = false
    | eval_form (@{code And} (p, q)) =
        eval_form p andalso eval_form q
    | eval_form (@{code Or} (p, q)) =
        eval_form p orelse eval_form q;
*}

text {*
  \noindent @{text code} takes as argument the name of a constant;  after the
  whole @{text SML} is read, the necessary code is generated transparently
  and the corresponding constant names are inserted.  This technique also
  allows to use pattern matching on constructors stemming from compiled
  @{text "datatypes"}.

  For a less simplistic example, theory @{theory Ferrack} is
  a good reference.
*}


subsection {* ML system interfaces \label{sec:ml} *}

text {*
  Since the code generator framework not only aims to provide
  a nice Isar interface but also to form a base for
  code-generation-based applications, here a short
  description of the most important ML interfaces.
*}

subsubsection {* Managing executable content *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Code.add_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code.del_eqn: "thm -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_pre: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.map_post: "(simpset -> simpset) -> theory -> theory"} \\
  @{index_ML Code_Preproc.add_functrans: "string * (theory -> (thm * bool) list -> (thm * bool) list option)
    -> theory -> theory"} \\
  @{index_ML Code_Preproc.del_functrans: "string -> theory -> theory"} \\
  @{index_ML Code.add_datatype: "(string * typ) list -> theory -> theory"} \\
  @{index_ML Code.get_type: "theory -> string
    -> (string * sort) list * ((string * string list) * typ list) list"} \\
  @{index_ML Code.get_type_of_constr_or_abstr: "theory -> string -> (string * bool) option"}
  \end{mldecls}

  \begin{description}

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

subsubsection {* Auxiliary *}

text %mlref {*
  \begin{mldecls}
  @{index_ML Code.read_const: "theory -> string -> string"}
  \end{mldecls}

  \begin{description}

  \item @{ML Code.read_const}~@{text thy}~@{text s}
     reads a constant as a concrete term expression @{text s}.

  \end{description}

*}

subsubsection {* Data depending on the theory's executable content *}

text {*
  Implementing code generator applications on top
  of the framework set out so far usually not only
  involves using those primitive interfaces
  but also storing code-dependent data and various
  other things.

  Due to incrementality of code generation, changes in the
  theory's executable content have to be propagated in a
  certain fashion.  Additionally, such changes may occur
  not only during theory extension but also during theory
  merge, which is a little bit nasty from an implementation
  point of view.  The framework provides a solution
  to this technical challenge by providing a functorial
  data slot @{ML_functor Code_Data}; on instantiation
  of this functor, the following types and operations
  are required:

  \medskip
  \begin{tabular}{l}
  @{text "type T"} \\
  @{text "val empty: T"} \\
  \end{tabular}

  \begin{description}

  \item @{text T} the type of data to store.

  \item @{text empty} initial (empty) data.

  \end{description}

  \noindent An instance of @{ML_functor Code_Data} provides the following
  interface:

  \medskip
  \begin{tabular}{l}
  @{text "change: theory \<rightarrow> (T \<rightarrow> T) \<rightarrow> T"} \\
  @{text "change_yield: theory \<rightarrow> (T \<rightarrow> 'a * T) \<rightarrow> 'a * T"}
  \end{tabular}

  \begin{description}

  \item @{text change} update of current data (cached!)
    by giving a continuation.

  \item @{text change_yield} update with side result.

  \end{description}
*}

end
