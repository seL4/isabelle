(*  Title:      HOL/Isar_examples/Cantor.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Cantor's Theorem *}

theory Cantor = Main:

text_raw {*
  \footnote{This is an Isar version of the final example of the
  Isabelle/HOL manual \cite{isabelle-HOL}.}
*}

text {*
  Cantor's Theorem states that every set has more subsets than it has
  elements.  It has become a favorite basic example in pure
  higher-order logic since it is so easily expressed: \[\all{f::\alpha
  \To \alpha \To \idt{bool}} \ex{S::\alpha \To \idt{bool}}
  \all{x::\alpha} f \ap x \not= S\]

  Viewing types as sets, $\alpha \To \idt{bool}$ represents the
  powerset of $\alpha$.  This version of the theorem states that for
  every function from $\alpha$ to its powerset, some subset is outside
  its range.  The Isabelle/Isar proofs below uses HOL's set theory,
  with the type $\alpha \ap \idt{set}$ and the operator
  $\idt{range}::(\alpha \To \beta) \To \beta \ap \idt{set}$.
*}

theorem "EX S. S ~: range (f :: 'a => 'a set)"
proof
  let ?S = "{x. x ~: f x}"
  show "?S ~: range f"
  proof
    assume "?S : range f"
    then obtain y where "?S = f y" ..
    thus False
    proof (rule equalityCE)
      assume "y : f y"
      assume "y : ?S" hence "y ~: f y" ..
      thus ?thesis by contradiction
    next
      assume "y ~: ?S"
      assume "y ~: f y" hence "y : ?S" ..
      thus ?thesis by contradiction
    qed
  qed
qed

text {*
  How much creativity is required?  As it happens, Isabelle can prove
  this theorem automatically using best-first search.  Depth-first
  search would diverge, but best-first search successfully navigates
  through the large search space.  The context of Isabelle's classical
  prover contains rules for the relevant constructs of HOL's set
  theory.
*}

theorem "EX S. S ~: range (f :: 'a => 'a set)"
  by best

text {*
  While this establishes the same theorem internally, we do not get
  any idea of how the proof actually works.  There is currently no way
  to transform internal system-level representations of Isabelle
  proofs back into Isar text.  Writing intelligible proof documents
  really is a creative process, after all.
*}

end
