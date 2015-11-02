(*  Title:      HOL/Isar_Examples/Cantor.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Cantor's Theorem\<close>

theory Cantor
imports Main
begin

text_raw \<open>\footnote{This is an Isar version of the final example of
  the Isabelle/HOL manual @{cite "isabelle-HOL"}.}\<close>

text \<open>Cantor's Theorem states that every set has more subsets than
  it has elements.  It has become a favourite basic example in pure
  higher-order logic since it is so easily expressed:

  @{text [display]
  \<open>\<forall>f::\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool. \<exists>S::\<alpha> \<Rightarrow> bool. \<forall>x::\<alpha>. f x \<noteq> S\<close>}

  Viewing types as sets, \<open>\<alpha> \<Rightarrow> bool\<close> represents the powerset of \<open>\<alpha>\<close>. This
  version of the theorem states that for every function from \<open>\<alpha>\<close> to its
  powerset, some subset is outside its range. The Isabelle/Isar proofs below
  uses HOL's set theory, with the type \<open>\<alpha> set\<close> and the operator
  \<open>range :: (\<alpha> \<Rightarrow> \<beta>) \<Rightarrow> \<beta> set\<close>.\<close>

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{x. x \<notin> f x}"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where "?S = f y" ..
    then show False
    proof (rule equalityCE)
      assume "y \<in> f y"
      assume "y \<in> ?S"
      then have "y \<notin> f y" ..
      with \<open>y : f y\<close> show ?thesis by contradiction
    next
      assume "y \<notin> ?S"
      assume "y \<notin> f y"
      then have "y \<in> ?S" ..
      with \<open>y \<notin> ?S\<close> show ?thesis by contradiction
    qed
  qed
qed

text \<open>How much creativity is required? As it happens, Isabelle can prove
  this theorem automatically using best-first search. Depth-first search
  would diverge, but best-first search successfully navigates through the
  large search space. The context of Isabelle's classical prover contains
  rules for the relevant constructs of HOL's set theory.\<close>

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  by best

text \<open>While this establishes the same theorem internally, we do not get any
  idea of how the proof actually works. There is currently no way to
  transform internal system-level representations of Isabelle proofs back
  into Isar text. Writing intelligible proof documents really is a creative
  process, after all.\<close>

end
