(*  Title:      HOL/Library/State_Monad.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section {* Combinator syntax for generic, open state monads (single-threaded monads) *}

theory State_Monad
imports Main Monad_Syntax
begin

subsection {* Motivation *}

text {*
  The logic HOL has no notion of constructor classes, so it is not
  possible to model monads the Haskell way in full genericity in
  Isabelle/HOL.
  
  However, this theory provides substantial support for a very common
  class of monads: \emph{state monads} (or \emph{single-threaded
  monads}, since a state is transformed single-threadedly).

  To enter from the Haskell world,
  @{url "http://www.engr.mun.ca/~theo/Misc/haskell_and_monads.htm"} makes
  a good motivating start.  Here we just sketch briefly how those
  monads enter the game of Isabelle/HOL.
*}

subsection {* State transformations and combinators *}

text {*
  We classify functions operating on states into two categories:

  \begin{description}

    \item[transformations] with type signature @{text "\<sigma> \<Rightarrow> \<sigma>'"},
      transforming a state.

    \item[``yielding'' transformations] with type signature @{text "\<sigma>
      \<Rightarrow> \<alpha> \<times> \<sigma>'"}, ``yielding'' a side result while transforming a
      state.

    \item[queries] with type signature @{text "\<sigma> \<Rightarrow> \<alpha>"}, computing a
      result dependent on a state.

  \end{description}

  By convention we write @{text "\<sigma>"} for types representing states and
  @{text "\<alpha>"}, @{text "\<beta>"}, @{text "\<gamma>"}, @{text "\<dots>"} for types
  representing side results.  Type changes due to transformations are
  not excluded in our scenario.

  We aim to assert that values of any state type @{text "\<sigma>"} are used
  in a single-threaded way: after application of a transformation on a
  value of type @{text "\<sigma>"}, the former value should not be used
  again.  To achieve this, we use a set of monad combinators:
*}

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

text {*
  Given two transformations @{term f} and @{term g}, they may be
  directly composed using the @{term "op \<circ>>"} combinator, forming a
  forward composition: @{prop "(f \<circ>> g) s = f (g s)"}.

  After any yielding transformation, we bind the side result
  immediately using a lambda abstraction.  This is the purpose of the
  @{term "op \<circ>\<rightarrow>"} combinator: @{prop "(f \<circ>\<rightarrow> (\<lambda>x. g)) s = (let (x, s')
  = f s in g s')"}.

  For queries, the existing @{term "Let"} is appropriate.

  Naturally, a computation may yield a side result by pairing it to
  the state from the left; we introduce the suggestive abbreviation
  @{term return} for this purpose.

  The most crucial distinction to Haskell is that we do not need to
  introduce distinguished type constructors for different kinds of
  state.  This has two consequences:

  \begin{itemize}

    \item The monad model does not state anything about the kind of
       state; the model for the state is completely orthogonal and may
       be specified completely independently.

    \item There is no distinguished type constructor encapsulating
       away the state transformation, i.e.~transformations may be
       applied directly without using any lifting or providing and
       dropping units (``open monad'').

    \item The type of states may change due to a transformation.

  \end{itemize}
*}


subsection {* Monad laws *}

text {*
  The common monadic laws hold and may also be used as normalization
  rules for monadic expressions:
*}

lemmas monad_simp = Pair_scomp scomp_Pair id_fcomp fcomp_id
  scomp_scomp scomp_fcomp fcomp_scomp fcomp_assoc

text {*
  Evaluation of monadic expressions by force:
*}

lemmas monad_collapse = monad_simp fcomp_apply scomp_apply split_beta


subsection {* Do-syntax *}

nonterminal sdo_binds and sdo_bind

syntax
  "_sdo_block" :: "sdo_binds \<Rightarrow> 'a" ("exec {//(2  _)//}" [12] 62)
  "_sdo_bind" :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(_ <-/ _)" 13)
  "_sdo_let" :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_sdo_then" :: "'a \<Rightarrow> sdo_bind" ("_" [14] 13)
  "_sdo_final" :: "'a \<Rightarrow> sdo_binds" ("_")
  "_sdo_cons" :: "[sdo_bind, sdo_binds] \<Rightarrow> sdo_binds" ("_;//_" [13, 12] 12)

syntax (xsymbols)
  "_sdo_bind"  :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(_ \<leftarrow>/ _)" 13)

translations
  "_sdo_block (_sdo_cons (_sdo_bind p t) (_sdo_final e))"
    == "CONST scomp t (\<lambda>p. e)"
  "_sdo_block (_sdo_cons (_sdo_then t) (_sdo_final e))"
    => "CONST fcomp t e"
  "_sdo_final (_sdo_block (_sdo_cons (_sdo_then t) (_sdo_final e)))"
    <= "_sdo_final (CONST fcomp t e)"
  "_sdo_block (_sdo_cons (_sdo_then t) e)"
    <= "CONST fcomp t (_sdo_block e)"
  "_sdo_block (_sdo_cons (_sdo_let p t) bs)"
    == "let p = t in _sdo_block bs"
  "_sdo_block (_sdo_cons b (_sdo_cons c cs))"
    == "_sdo_block (_sdo_cons b (_sdo_final (_sdo_block (_sdo_cons c cs))))"
  "_sdo_cons (_sdo_let p t) (_sdo_final s)"
    == "_sdo_final (let p = t in s)"
  "_sdo_block (_sdo_final e)" => "e"

text {*
  For an example, see @{file "~~/src/HOL/Proofs/Extraction/Higman.thy"}.
*}

end
