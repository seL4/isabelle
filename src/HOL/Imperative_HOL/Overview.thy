(*  Title:      HOL/Imperative_HOL/Overview.thy
    Author:     Florian Haftmann, TU Muenchen
*)

(*<*)
theory Overview
imports Imperative_HOL "~~/src/HOL/Library/LaTeXsugar"
begin

(* type constraints with spacing *)
setup {*
let
  val typ = Simple_Syntax.read_typ;
in
  Sign.del_syntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_\<Colon>_", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_\<Colon>_", [4, 0], 3))] #>
  Sign.add_syntax (Symbol.xsymbolsN, false)
   [("_constrain", typ "logic => type => logic", Mixfix ("_ \<Colon>  _", [4, 0], 3)),
    ("_constrain", typ "prop' => type => prop'", Mixfix ("_ \<Colon> _", [4, 0], 3))]
end
*}(*>*)

text {*
  @{text "Imperative HOL"} is a leightweight framework for reasoning
  about imperative data structures in @{text "Isabelle/HOL"}
  \cite{Nipkow-et-al:2002:tutorial}.  Its basic ideas are described in
  \cite{Bulwahn-et-al:2008:imp_HOL}.  However their concrete
  realisation has changed since, due to both extensions and
  refinements.  Therefore this overview wants to present the framework
  \qt{as it is} by now.  It focusses on the user-view, less on matters
  of construction.  For details study of the theory sources is
  encouraged.
*}


section {* A polymorphic heap inside a monad *}

text {*
  Heaps (@{type heap}) can be populated by values of class @{class
  heap}; HOL's default types are already instantiated to class @{class
  heap}.  Class @{class heap} is a subclass of @{class countable};  see
  theory @{text Countable} for ways to instantiate types as @{class countable}.

  The heap is wrapped up in a monad @{typ "'a Heap"} by means of the
  following specification:

  \begin{quote}
    @{datatype Heap}
  \end{quote}

  Unwrapping of this monad type happens through

  \begin{quote}
    @{term_type execute} \\
    @{thm execute.simps [no_vars]}
  \end{quote}

  This allows for equational reasoning about monadic expressions; the
  fact collection @{text execute_simps} contains appropriate rewrites
  for all fundamental operations.

  Primitive fine-granular control over heaps is available through rule
  @{text Heap_cases}:

  \begin{quote}
    @{thm [break] Heap_cases [no_vars]}
  \end{quote}

  Monadic expression involve the usual combinators:

  \begin{quote}
    @{term_type return} \\
    @{term_type bind} \\
    @{term_type raise}
  \end{quote}

  This is also associated with nice monad do-syntax.  The @{typ
  string} argument to @{const raise} is just a codified comment.

  Among a couple of generic combinators the following is helpful for
  establishing invariants:

  \begin{quote}
    @{term_type assert} \\
    @{thm assert_def [no_vars]}
  \end{quote}
*}


section {* Relational reasoning about @{type Heap} expressions *}

text {*
  To establish correctness of imperative programs, predicate

  \begin{quote}
    @{term_type effect}
  \end{quote}

  provides a simple relational calculus.  Primitive rules are @{text
  effectI} and @{text effectE}, rules appropriate for reasoning about
  imperative operations are available in the @{text effect_intros} and
  @{text effect_elims} fact collections.

  Often non-failure of imperative computations does not depend
  on the heap at all;  reasoning then can be easier using predicate

  \begin{quote}
    @{term_type success}
  \end{quote}

  Introduction rules for @{const success} are available in the
  @{text success_intro} fact collection.

  @{const execute}, @{const effect}, @{const success} and @{const bind}
  are related by rules @{text execute_bind_success}, @{text
  success_bind_executeI}, @{text success_bind_effectI}, @{text
  effect_bindI}, @{text effect_bindE} and @{text execute_bind_eq_SomeI}.
*}


section {* Monadic data structures *}

text {*
  The operations for monadic data structures (arrays and references)
  come in two flavours:

  \begin{itemize}

     \item Operations on the bare heap; their number is kept minimal
       to facilitate proving.

     \item Operations on the heap wrapped up in a monad; these are designed
       for executing.

  \end{itemize}

  Provided proof rules are such that they reduce monad operations to
  operations on bare heaps.

  Note that HOL equality coincides with reference equality and may be
  used as primitive executable operation.
*}

subsection {* Arrays *}

text {*
  Heap operations:

  \begin{quote}
    @{term_type Array.alloc} \\
    @{term_type Array.present} \\
    @{term_type Array.get} \\
    @{term_type Array.set} \\
    @{term_type Array.length} \\
    @{term_type Array.update} \\
    @{term_type Array.noteq}
  \end{quote}

  Monad operations:

  \begin{quote}
    @{term_type Array.new} \\
    @{term_type Array.of_list} \\
    @{term_type Array.make} \\
    @{term_type Array.len} \\
    @{term_type Array.nth} \\
    @{term_type Array.upd} \\
    @{term_type Array.map_entry} \\
    @{term_type Array.swap} \\
    @{term_type Array.freeze}
  \end{quote}
*}

subsection {* References *}

text {*
  Heap operations:

  \begin{quote}
    @{term_type Ref.alloc} \\
    @{term_type Ref.present} \\
    @{term_type Ref.get} \\
    @{term_type Ref.set} \\
    @{term_type Ref.noteq}
  \end{quote}

  Monad operations:

  \begin{quote}
    @{term_type Ref.ref} \\
    @{term_type Ref.lookup} \\
    @{term_type Ref.update} \\
    @{term_type Ref.change}
  \end{quote}
*}


section {* Code generation *}

text {*
  Imperative HOL sets up the code generator in a way that imperative
  operations are mapped to suitable counterparts in the target
  language.  For @{text Haskell}, a suitable @{text ST} monad is used;
  for @{text SML}, @{text Ocaml} and @{text Scala} unit values ensure
  that the evaluation order is the same as you would expect from the
  original monadic expressions.  These units may look cumbersome; the
  target language variants @{text SML_imp}, @{text Ocaml_imp} and
  @{text Scala_imp} make some effort to optimize some of them away.
*}


section {* Some hints for using the framework *}

text {*
  Of course a framework itself does not by itself indicate how to make
  best use of it.  Here some hints drawn from prior experiences with
  Imperative HOL:

  \begin{itemize}

    \item Proofs on bare heaps should be strictly separated from those
      for monadic expressions.  The first capture the essence, while the
      latter just describe a certain wrapping-up.

    \item A good methodology is to gradually improve an imperative
      program from a functional one.  In the extreme case this means
      that an original functional program is decomposed into suitable
      operations with exactly one corresponding imperative operation.
      Having shown suitable correspondence lemmas between those, the
      correctness prove of the whole imperative program simply
      consists of composing those.
      
    \item Whether one should prefer equational reasoning (fact
      collection @{text execute_simps} or relational reasoning (fact
      collections @{text effect_intros} and @{text effect_elims}) depends
      on the problems to solve.  For complex expressions or
      expressions involving binders, the relation style usually is
      superior but requires more proof text.

    \item Note that you can extend the fact collections of Imperative
      HOL yourself whenever appropriate.

  \end{itemize}
*}

end