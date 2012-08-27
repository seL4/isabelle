theory Evaluation
imports Setup
begin

section {* Evaluation \label{sec:evaluation} *}

text {*
  Recalling \secref{sec:principle}, code generation turns a system of
  equations into a program with the \emph{same} equational semantics.
  As a consequence, this program can be used as a \emph{rewrite
  engine} for terms: rewriting a term @{term "t"} using a program to a
  term @{term "t'"} yields the theorems @{prop "t \<equiv> t'"}.  This
  application of code generation in the following is referred to as
  \emph{evaluation}.
*}


subsection {* Evaluation techniques *}

text {*
  The existing infrastructure provides a rich palette of evaluation
  techniques, each comprising different aspects:

  \begin{description}

    \item[Expressiveness.]  Depending on how good symbolic computation
      is supported, the class of terms which can be evaluated may be
      bigger or smaller.

    \item[Efficiency.]  The more machine-near the technique, the
      faster it is.

    \item[Trustability.]  Techniques which a huge (and also probably
      more configurable infrastructure) are more fragile and less
      trustable.

  \end{description}
*}


subsubsection {* The simplifier (@{text simp}) *}

text {*
  The simplest way for evaluation is just using the simplifier with
  the original code equations of the underlying program.  This gives
  fully symbolic evaluation and highest trustablity, with the usual
  performance of the simplifier.  Note that for operations on abstract
  datatypes (cf.~\secref{sec:invariant}), the original theorems as
  given by the users are used, not the modified ones.
*}


subsubsection {* Normalization by evaluation (@{text nbe}) *}

text {*
  Normalization by evaluation \cite{Aehlig-Haftmann-Nipkow:2008:nbe}
  provides a comparably fast partially symbolic evaluation which
  permits also normalization of functions and uninterpreted symbols;
  the stack of code to be trusted is considerable.
*}


subsubsection {* Evaluation in ML (@{text code}) *}

text {*
  Highest performance can be achieved by evaluation in ML, at the cost
  of being restricted to ground results and a layered stack of code to
  be trusted, including code generator configurations by the user.

  Evaluation is carried out in a target language \emph{Eval} which
  inherits from \emph{SML} but for convenience uses parts of the
  Isabelle runtime environment.  The soundness of computation carried
  out there depends crucially on the correctness of the code
  generator setup; this is one of the reasons why you should not use
  adaptation (see \secref{sec:adaptation}) frivolously.
*}


subsection {* Aspects of evaluation *}

text {*
  Each of the techniques can be combined with different aspects.  The
  most important distinction is between dynamic and static evaluation.
  Dynamic evaluation takes the code generator configuration \qt{as it
  is} at the point where evaluation is issued.  Best example is the
  @{command_def value} command which allows ad-hoc evaluation of
  terms:
*}

value %quote "42 / (12 :: rat)"

text {*
  \noindent By default @{command value} tries all available evaluation
  techniques and prints the result of the first succeeding one.  A particular
  technique may be specified in square brackets, e.g.
*}

value %quote [nbe] "42 / (12 :: rat)"

text {*
  To employ dynamic evaluation in the document generation, there is also
  a @{text value} antiquotation. By default, it also tries all available evaluation
  techniques and prints the result of the first succeeding one, unless a particular
  technique is specified in square brackets.

  Static evaluation freezes the code generator configuration at a
  certain point and uses this context whenever evaluation is issued
  later on.  This is particularly appropriate for proof procedures
  which use evaluation, since then the behaviour of evaluation is not
  changed or even compromised later on by actions of the user.

  As a technical complication, terms after evaluation in ML must be
  turned into Isabelle's internal term representation again.  Since
  this is also configurable, it is never fully trusted.  For this
  reason, evaluation in ML comes with further aspects:

  \begin{description}

    \item[Plain evaluation.]  A term is normalized using the provided
      term reconstruction from ML to Isabelle; for applications which
      do not need to be fully trusted.

    \item[Property conversion.]  Evaluates propositions; since these
      are monomorphic, the term reconstruction is fixed once and for all
      and therefore trustable.

    \item[Conversion.]  Evaluates an arbitrary term @{term "t"} first
      by plain evaluation and certifies the result @{term "t'"} by
      checking the equation @{term "t \<equiv> t'"} using property
      conversion.

  \end{description}

  \noindent The picture is further complicated by the roles of
  exceptions.  Here three cases have to be distinguished:

  \begin{itemize}

    \item Evaluation of @{term t} terminates with a result @{term
      "t'"}.

    \item Evaluation of @{term t} terminates which en exception
      indicating a pattern match failure or a non-implemented
      function.  As sketched in \secref{sec:partiality}, this can be
      interpreted as partiality.
     
    \item Evaluation raises any other kind of exception.
     
  \end{itemize}

  \noindent For conversions, the first case yields the equation @{term
  "t = t'"}, the second defaults to reflexivity @{term "t = t"}.
  Exceptions of the third kind are propagated to the user.

  By default return values of plain evaluation are optional, yielding
  @{text "SOME t'"} in the first case, @{text "NONE"} in the
  second, and propagating the exception in the third case.  A strict
  variant of plain evaluation either yields @{text "t'"} or propagates
  any exception, a liberal variant caputures any exception in a result
  of type @{text "Exn.result"}.
  
  For property conversion (which coincides with conversion except for
  evaluation in ML), methods are provided which solve a given goal by
  evaluation.
*}


subsection {* Schematic overview *}

text {*
  \newcommand{\ttsize}{\fontsize{5.8pt}{8pt}\selectfont}
  \fontsize{9pt}{12pt}\selectfont
  \begin{tabular}{ll||c|c|c}
    & & @{text simp} & @{text nbe} & @{text code} \tabularnewline \hline \hline
    \multirow{5}{1ex}{\rotatebox{90}{dynamic}}
      & interactive evaluation 
      & @{command value} @{text "[simp]"} & @{command value} @{text "[nbe]"} & @{command value} @{text "[code]"}
      \tabularnewline
    & plain evaluation & & & \ttsize@{ML "Code_Evaluation.dynamic_value"} \tabularnewline \cline{2-5}
    & evaluation method & @{method code_simp} & @{method normalization} & @{method eval} \tabularnewline
    & property conversion & & & \ttsize@{ML "Code_Runtime.dynamic_holds_conv"} \tabularnewline \cline{2-5}
    & conversion & \ttsize@{ML "Code_Simp.dynamic_conv"} & \ttsize@{ML "Nbe.dynamic_conv"}
      & \ttsize@{ML "Code_Evaluation.dynamic_conv"} \tabularnewline \hline \hline
    \multirow{3}{1ex}{\rotatebox{90}{static}}
    & plain evaluation & & & \ttsize@{ML "Code_Evaluation.static_value"} \tabularnewline \cline{2-5}
    & property conversion & &
      & \ttsize@{ML "Code_Runtime.static_holds_conv"} \tabularnewline \cline{2-5}
    & conversion & \ttsize@{ML "Code_Simp.static_conv"}
      & \ttsize@{ML "Nbe.static_conv"}
      & \ttsize@{ML "Code_Evaluation.static_conv"}
  \end{tabular}
*}


subsection {* Intimate connection between logic and system runtime *}

text {*
  The toolbox of static evaluation conversions forms a reasonable base
  to interweave generated code and system tools.  However in some
  situations more direct interaction is desirable.
*}


subsubsection {* Static embedding of generated code into system runtime -- the @{text code} antiquotation *}

text {*
  The @{text code} antiquotation allows to include constants from
  generated code directly into ML system code, as in the following toy
  example:
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
  \noindent @{text code} takes as argument the name of a constant;
  after the whole ML is read, the necessary code is generated
  transparently and the corresponding constant names are inserted.
  This technique also allows to use pattern matching on constructors
  stemming from compiled datatypes.  Note that the @{text code}
  antiquotation may not refer to constants which carry adaptations;
  here you have to refer to the corresponding adapted code directly.

  For a less simplistic example, theory @{text Approximation} in
  the @{text Decision_Procs} session is a good reference.
*}


subsubsection {* Static embedding of generated code into system runtime -- @{text code_reflect} *}

text {*
  The @{text code} antiquoation is lightweight, but the generated code
  is only accessible while the ML section is processed.  Sometimes this
  is not appropriate, especially if the generated code contains datatype
  declarations which are shared with other parts of the system.  In these
  cases, @{command_def code_reflect} can be used:
*}

code_reflect %quote Sum_Type
  datatypes sum = Inl | Inr
  functions "Sum_Type.Projl" "Sum_Type.Projr"

text {*
  \noindent @{command_def code_reflect} takes a structure name and
  references to datatypes and functions; for these code is compiled
  into the named ML structure and the \emph{Eval} target is modified
  in a way that future code generation will reference these
  precompiled versions of the given datatypes and functions.  This
  also allows to refer to the referenced datatypes and functions from
  arbitrary ML code as well.

  A typical example for @{command code_reflect} can be found in the
  @{theory Predicate} theory.
*}


subsubsection {* Separate compilation -- @{text code_reflect} *}

text {*
  For technical reasons it is sometimes necessary to separate
  generation and compilation of code which is supposed to be used in
  the system runtime.  For this @{command code_reflect} with an
  optional @{text "file"} argument can be used:
*}

code_reflect %quote Rat
  datatypes rat = Frct
  functions Fract
    "(plus :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(minus :: rat \<Rightarrow> rat \<Rightarrow> rat)"
    "(times :: rat \<Rightarrow> rat \<Rightarrow> rat)" "(divide :: rat \<Rightarrow> rat \<Rightarrow> rat)"
  file "examples/rat.ML"

text {*
  \noindent This merely generates the referenced code to the given
  file which can be included into the system runtime later on.
*}

end

