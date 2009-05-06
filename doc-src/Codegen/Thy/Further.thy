theory Further
imports Setup
begin

section {* Further issues \label{sec:further} *}

subsection {* Further reading *}

text {*
  Do dive deeper into the issue of code generation, you should visit
  the Isabelle/Isar Reference Manual \cite{isabelle-isar-ref} which
  contains exhaustive syntax diagrams.
*}

subsection {* Modules *}

text {*
  When invoking the @{command export_code} command it is possible to leave
  out the @{keyword "module_name"} part;  then code is distributed over
  different modules, where the module name space roughly is induced
  by the @{text Isabelle} theory name space.

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

text {*
  we explicitly map all those modules on \emph{ABC},
  resulting in an ad-hoc merge of this three modules
  at serialisation time.
*}

subsection {* Evaluation oracle *}

text {*
  Code generation may also be used to \emph{evaluate} expressions
  (using @{text SML} as target language of course).
  For instance, the @{command value} allows to reduce an expression to a
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

subsection {* Code antiquotation *}

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
  @{text datatypes}.

  For a less simplistic example, theory @{theory Ferrack} is
  a good reference.
*}

subsection {* Imperative data structures *}

text {*
  If you consider imperative data structures as inevitable for a specific
  application, you should consider
  \emph{Imperative Functional Programming with Isabelle/HOL}
  (\cite{bulwahn-et-al:2008:imperative});
  the framework described there is available in theory @{theory Imperative_HOL}.
*}

end
