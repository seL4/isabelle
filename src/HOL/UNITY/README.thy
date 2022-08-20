theory README imports Main
begin

section \<open>UNITY--Chandy and Misra's UNITY formalism\<close>

text \<open>
  The book \<^emph>\<open>Parallel Program Design: A Foundation\<close> by Chandy and Misra
  (Addison-Wesley, 1988) presents the UNITY formalism. UNITY consists of an
  abstract programming language of guarded assignments and a calculus for
  reasoning about such programs. Misra's 1994 paper "A Logic for Concurrent
  Programming" presents New UNITY, giving more elegant foundations for a more
  general class of languages. In recent work, Chandy and Sanders have proposed
  new methods for reasoning about systems composed of many components.

  This directory formalizes these new ideas for UNITY. The Isabelle examples
  may seem strange to UNITY traditionalists. Hand UNITY proofs tend to be
  written in the forwards direction, as in informal mathematics, while
  Isabelle works best in a backwards (goal-directed) style. Programs are
  expressed as sets of commands, where each command is a relation on states.
  Quantification over commands using \<^verbatim>\<open>[]\<close> is easily expressed. At present,
  there are no examples of quantification using \<^verbatim>\<open>||\<close>.

  A UNITY assertion denotes the set of programs satisfying it, as in the
  propositions-as-types paradigm. The resulting style is readable if
  unconventional.

  Safety proofs (invariants) are often proved automatically. Progress proofs
  involving ENSURES can sometimes be proved automatically. The level of
  automation appears to be about the same as in HOL-UNITY by Flemming Andersen
  et al.

  The directory \<^dir>\<open>Simple\<close> presents a few examples, mostly taken from Misra's
  1994 paper, involving single programs. The directory \<^dir>\<open>Comp\<close> presents
  examples of proofs involving program composition.
\<close>

end
