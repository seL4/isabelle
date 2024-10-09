(*  Title:      HOL/Imperative_HOL/Overview.thy
    Author:     Florian Haftmann, TU Muenchen
*)

(*<*)
theory Overview
imports Imperative_HOL "HOL-Library.LaTeXsugar"
begin

unbundle constrain_space_syntax
(*>*)

text \<open>
  \<open>Imperative HOL\<close> is a lightweight framework for reasoning
  about imperative data structures in \<open>Isabelle/HOL\<close>
  \<^cite>\<open>"Nipkow-et-al:2002:tutorial"\<close>.  Its basic ideas are described in
  \<^cite>\<open>"Bulwahn-et-al:2008:imp_HOL"\<close>.  However their concrete
  realisation has changed since, due to both extensions and
  refinements.  Therefore this overview wants to present the framework
  \qt{as it is} by now.  It focusses on the user-view, less on matters
  of construction.  For details study of the theory sources is
  encouraged.
\<close>


section \<open>A polymorphic heap inside a monad\<close>

text \<open>
  Heaps (\<^type>\<open>heap\<close>) can be populated by values of class \<^class>\<open>heap\<close>; HOL's default types are
  already instantiated to class \<^class>\<open>heap\<close>.  Class \<^class>\<open>heap\<close> is a subclass of \<^class>\<open>countable\<close>;
  see theory \<open>Countable\<close> for ways to instantiate types as \<^class>\<open>countable\<close>.

  The heap is wrapped up in a monad \<^typ>\<open>'a Heap\<close> by means of the
  following specification:

  \begin{quote}
    \<^datatype>\<open>Heap\<close>
  \end{quote}

  Unwrapping of this monad type happens through

  \begin{quote}
    \<^term_type>\<open>execute\<close> \\
    @{thm execute.simps [no_vars]}
  \end{quote}

  This allows for equational reasoning about monadic expressions; the
  fact collection \<open>execute_simps\<close> contains appropriate rewrites
  for all fundamental operations.

  Primitive fine-granular control over heaps is available through rule
  \<open>Heap_cases\<close>:

  \begin{quote}
    @{thm [break] Heap_cases [no_vars]}
  \end{quote}

  Monadic expression involve the usual combinators:

  \begin{quote}
    \<^term_type>\<open>return\<close> \\
    \<^term_type>\<open>bind\<close> \\
    \<^term_type>\<open>raise\<close>
  \end{quote}

  This is also associated with nice monad do-syntax.  The \<^typ>\<open>string\<close> argument to \<^const>\<open>raise\<close> is
  just a codified comment.

  Among a couple of generic combinators the following is helpful for
  establishing invariants:

  \begin{quote}
    \<^term_type>\<open>assert\<close> \\
    @{thm assert_def [no_vars]}
  \end{quote}
\<close>


section \<open>Relational reasoning about \<^type>\<open>Heap\<close> expressions\<close>

text \<open>
  To establish correctness of imperative programs, predicate

  \begin{quote}
    \<^term_type>\<open>effect\<close>
  \end{quote}

  provides a simple relational calculus.  Primitive rules are \<open>effectI\<close> and \<open>effectE\<close>, rules
  appropriate for reasoning about imperative operations are available in the \<open>effect_intros\<close> and
  \<open>effect_elims\<close> fact collections.

  Often non-failure of imperative computations does not depend
  on the heap at all;  reasoning then can be easier using predicate

  \begin{quote}
    \<^term_type>\<open>success\<close>
  \end{quote}

  Introduction rules for \<^const>\<open>success\<close> are available in the
  \<open>success_intro\<close> fact collection.

  \<^const>\<open>execute\<close>, \<^const>\<open>effect\<close>, \<^const>\<open>success\<close> and \<^const>\<open>bind\<close>
  are related by rules \<open>execute_bind_success\<close>, \<open>success_bind_executeI\<close>, \<open>success_bind_effectI\<close>,
  \<open>effect_bindI\<close>, \<open>effect_bindE\<close> and \<open>execute_bind_eq_SomeI\<close>.
\<close>


section \<open>Monadic data structures\<close>

text \<open>
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
\<close>

subsection \<open>Arrays\<close>

text \<open>
  Heap operations:

  \begin{quote}
    \<^term_type>\<open>Array.alloc\<close> \\
    \<^term_type>\<open>Array.present\<close> \\
    \<^term_type>\<open>Array.get\<close> \\
    \<^term_type>\<open>Array.set\<close> \\
    \<^term_type>\<open>Array.length\<close> \\
    \<^term_type>\<open>Array.update\<close> \\
    \<^term_type>\<open>Array.noteq\<close>
  \end{quote}

  Monad operations:

  \begin{quote}
    \<^term_type>\<open>Array.new\<close> \\
    \<^term_type>\<open>Array.of_list\<close> \\
    \<^term_type>\<open>Array.make\<close> \\
    \<^term_type>\<open>Array.len\<close> \\
    \<^term_type>\<open>Array.nth\<close> \\
    \<^term_type>\<open>Array.upd\<close> \\
    \<^term_type>\<open>Array.map_entry\<close> \\
    \<^term_type>\<open>Array.swap\<close> \\
    \<^term_type>\<open>Array.freeze\<close>
  \end{quote}
\<close>

subsection \<open>References\<close>

text \<open>
  Heap operations:

  \begin{quote}
    \<^term_type>\<open>Ref.alloc\<close> \\
    \<^term_type>\<open>Ref.present\<close> \\
    \<^term_type>\<open>Ref.get\<close> \\
    \<^term_type>\<open>Ref.set\<close> \\
    \<^term_type>\<open>Ref.noteq\<close>
  \end{quote}

  Monad operations:

  \begin{quote}
    \<^term_type>\<open>Ref.ref\<close> \\
    \<^term_type>\<open>Ref.lookup\<close> \\
    \<^term_type>\<open>Ref.update\<close> \\
    \<^term_type>\<open>Ref.change\<close>
  \end{quote}
\<close>


section \<open>Code generation\<close>

text \<open>
  Imperative HOL sets up the code generator in a way that imperative
  operations are mapped to suitable counterparts in the target
  language.  For \<open>Haskell\<close>, a suitable \<open>ST\<close> monad is used;
  for \<open>SML\<close>, \<open>Ocaml\<close> and \<open>Scala\<close> unit values ensure
  that the evaluation order is the same as you would expect from the
  original monadic expressions.  These units may look cumbersome; the
  target language variants \<open>SML_imp\<close>, \<open>Ocaml_imp\<close> and
  \<open>Scala_imp\<close> make some effort to optimize some of them away.
\<close>


section \<open>Some hints for using the framework\<close>

text \<open>
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
      collection \<open>execute_simps\<close> or relational reasoning (fact
      collections \<open>effect_intros\<close> and \<open>effect_elims\<close>) depends
      on the problems to solve.  For complex expressions or
      expressions involving binders, the relation style is usually
      superior but requires more proof text.

    \item Note that you can extend the fact collections of Imperative
      HOL yourself whenever appropriate.

  \end{itemize}
\<close>

end
