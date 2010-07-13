(*  Title:      HOL/Library/State_Monad.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Combinator syntax for generic, open state monads (single threaded monads) *}

theory State_Monad
imports Monad_Syntax
begin

subsection {* Motivation *}

text {*
  The logic HOL has no notion of constructor classes, so
  it is not possible to model monads the Haskell way
  in full genericity in Isabelle/HOL.
  
  However, this theory provides substantial support for
  a very common class of monads: \emph{state monads}
  (or \emph{single-threaded monads}, since a state
  is transformed single-threaded).

  To enter from the Haskell world,
  \url{http://www.engr.mun.ca/~theo/Misc/haskell_and_monads.htm}
  makes a good motivating start.  Here we just sketch briefly
  how those monads enter the game of Isabelle/HOL.
*}

subsection {* State transformations and combinators *}

text {*
  We classify functions operating on states into two categories:

  \begin{description}
    \item[transformations]
      with type signature @{text "\<sigma> \<Rightarrow> \<sigma>'"},
      transforming a state.
    \item[``yielding'' transformations]
      with type signature @{text "\<sigma> \<Rightarrow> \<alpha> \<times> \<sigma>'"},
      ``yielding'' a side result while transforming a state.
    \item[queries]
      with type signature @{text "\<sigma> \<Rightarrow> \<alpha>"},
      computing a result dependent on a state.
  \end{description}

  By convention we write @{text "\<sigma>"} for types representing states
  and @{text "\<alpha>"}, @{text "\<beta>"}, @{text "\<gamma>"}, @{text "\<dots>"}
  for types representing side results.  Type changes due
  to transformations are not excluded in our scenario.

  We aim to assert that values of any state type @{text "\<sigma>"}
  are used in a single-threaded way: after application
  of a transformation on a value of type @{text "\<sigma>"}, the
  former value should not be used again.  To achieve this,
  we use a set of monad combinators:
*}

notation fcomp (infixl "\<circ>>" 60)
notation (xsymbols) fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "o->" 60)
notation (xsymbols) scomp (infixl "\<circ>\<rightarrow>" 60)

abbreviation (input)
  "return \<equiv> Pair"

text {*
  Given two transformations @{term f} and @{term g}, they
  may be directly composed using the @{term "op \<circ>>"} combinator,
  forming a forward composition: @{prop "(f \<circ>> g) s = f (g s)"}.

  After any yielding transformation, we bind the side result
  immediately using a lambda abstraction.  This 
  is the purpose of the @{term "op \<circ>\<rightarrow>"} combinator:
  @{prop "(f \<circ>\<rightarrow> (\<lambda>x. g)) s = (let (x, s') = f s in g s')"}.

  For queries, the existing @{term "Let"} is appropriate.

  Naturally, a computation may yield a side result by pairing
  it to the state from the left;  we introduce the
  suggestive abbreviation @{term return} for this purpose.

  The most crucial distinction to Haskell is that we do
  not need to introduce distinguished type constructors
  for different kinds of state.  This has two consequences:
  \begin{itemize}
    \item The monad model does not state anything about
       the kind of state; the model for the state is
       completely orthogonal and may be
       specified completely independently.
    \item There is no distinguished type constructor
       encapsulating away the state transformation, i.e.~transformations
       may be applied directly without using any lifting
       or providing and dropping units (``open monad'').
    \item The type of states may change due to a transformation.
  \end{itemize}
*}


subsection {* Monad laws *}

text {*
  The common monadic laws hold and may also be used
  as normalization rules for monadic expressions:
*}

lemmas monad_simp = Pair_scomp scomp_Pair id_fcomp fcomp_id
  scomp_scomp scomp_fcomp fcomp_scomp fcomp_assoc

text {*
  Evaluation of monadic expressions by force:
*}

lemmas monad_collapse = monad_simp fcomp_apply scomp_apply split_beta

setup {*
  Adhoc_Overloading.add_variant @{const_name bindM} @{const_name scomp}
*}

text {*
  For an example, see HOL/Extraction/Higman.thy.
*}

end
