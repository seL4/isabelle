theory Evaluation
imports Setup
begin

section {* Evaluation *}

text {* Introduction *}


subsection {* Evaluation techniques *}

text {* simplifier *}

text {* nbe *}

text {* eval target: SML standalone vs. Isabelle/SML, example, soundness *}


subsection {* Dynamic evaluation *}

text {* value (three variants) *}

text {* methods (three variants) *}

text {* corresponding ML interfaces *}


subsection {* Static evaluation *}

text {* code_simp, nbe (tbd), Eval (tbd, in simple fashion) *}

text {* hand-written: code antiquotation *}


subsection {* Hybrid techniques *}

text {* code reflect runtime *}

text {* code reflect external *}


text {* FIXME here the old sections follow *}

subsection {* Evaluation oracle *}

text {*
  Code generation may also be used to \emph{evaluate} expressions
  (using @{text SML} as target language of course).
  For instance, the @{command_def value} reduces an expression to a
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

  For a less simplistic example, theory @{text Ferrack} is
  a good reference.
*}


end
