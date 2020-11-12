(*  Title:      HOL/Library/Open_State_Syntax.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Combinator syntax for generic, open state monads (single-threaded monads)\<close>

theory Open_State_Syntax
imports Main
begin

context
  includes state_combinator_syntax
begin

subsection \<open>Motivation\<close>

text \<open>
  The logic HOL has no notion of constructor classes, so it is not
  possible to model monads the Haskell way in full genericity in
  Isabelle/HOL.
  
  However, this theory provides substantial support for a very common
  class of monads: \emph{state monads} (or \emph{single-threaded
  monads}, since a state is transformed single-threadedly).

  To enter from the Haskell world,
  \<^url>\<open>https://www.engr.mun.ca/~theo/Misc/haskell_and_monads.htm\<close> makes
  a good motivating start.  Here we just sketch briefly how those
  monads enter the game of Isabelle/HOL.
\<close>

subsection \<open>State transformations and combinators\<close>

text \<open>
  We classify functions operating on states into two categories:

  \begin{description}

    \item[transformations] with type signature \<open>\<sigma> \<Rightarrow> \<sigma>'\<close>,
      transforming a state.

    \item[``yielding'' transformations] with type signature \<open>\<sigma>
      \<Rightarrow> \<alpha> \<times> \<sigma>'\<close>, ``yielding'' a side result while transforming a
      state.

    \item[queries] with type signature \<open>\<sigma> \<Rightarrow> \<alpha>\<close>, computing a
      result dependent on a state.

  \end{description}

  By convention we write \<open>\<sigma>\<close> for types representing states and
  \<open>\<alpha>\<close>, \<open>\<beta>\<close>, \<open>\<gamma>\<close>, \<open>\<dots>\<close> for types
  representing side results.  Type changes due to transformations are
  not excluded in our scenario.

  We aim to assert that values of any state type \<open>\<sigma>\<close> are used
  in a single-threaded way: after application of a transformation on a
  value of type \<open>\<sigma>\<close>, the former value should not be used
  again.  To achieve this, we use a set of monad combinators:
\<close>

text \<open>
  Given two transformations \<^term>\<open>f\<close> and \<^term>\<open>g\<close>, they may be
  directly composed using the \<^term>\<open>(\<circ>>)\<close> combinator, forming a
  forward composition: \<^prop>\<open>(f \<circ>> g) s = f (g s)\<close>.

  After any yielding transformation, we bind the side result
  immediately using a lambda abstraction.  This is the purpose of the
  \<^term>\<open>(\<circ>\<rightarrow>)\<close> combinator: \<^prop>\<open>(f \<circ>\<rightarrow> (\<lambda>x. g)) s = (let (x, s')
  = f s in g s')\<close>.

  For queries, the existing \<^term>\<open>Let\<close> is appropriate.

  Naturally, a computation may yield a side result by pairing it to
  the state from the left; we introduce the suggestive abbreviation
  \<^term>\<open>return\<close> for this purpose.

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
\<close>


subsection \<open>Monad laws\<close>

text \<open>
  The common monadic laws hold and may also be used as normalization
  rules for monadic expressions:
\<close>

lemmas monad_simp = Pair_scomp scomp_Pair id_fcomp fcomp_id
  scomp_scomp scomp_fcomp fcomp_scomp fcomp_assoc

text \<open>
  Evaluation of monadic expressions by force:
\<close>

lemmas monad_collapse = monad_simp fcomp_apply scomp_apply split_beta

end


subsection \<open>Do-syntax\<close>

nonterminal sdo_binds and sdo_bind

syntax
  "_sdo_block" :: "sdo_binds \<Rightarrow> 'a" ("exec {//(2  _)//}" [12] 62)
  "_sdo_bind"  :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(_ \<leftarrow>/ _)" 13)
  "_sdo_let" :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_sdo_then" :: "'a \<Rightarrow> sdo_bind" ("_" [14] 13)
  "_sdo_final" :: "'a \<Rightarrow> sdo_binds" ("_")
  "_sdo_cons" :: "[sdo_bind, sdo_binds] \<Rightarrow> sdo_binds" ("_;//_" [13, 12] 12)

syntax (ASCII)
  "_sdo_bind" :: "[pttrn, 'a] \<Rightarrow> sdo_bind" ("(_ <-/ _)" 13)

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

text \<open>
  For an example, see \<^file>\<open>~~/src/HOL/Proofs/Extraction/Higman_Extraction.thy\<close>.
\<close>

end
