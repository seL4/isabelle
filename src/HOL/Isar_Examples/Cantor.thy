(*  Title:      HOL/Isar_Examples/Cantor.thy
    Author:     Makarius
*)

section \<open>Cantor's Theorem\<close>

theory Cantor
imports Main
begin

text \<open>
  Cantor's Theorem states that there is no surjection from
  a set to its powerset.  The proof works by diagonalization.  E.g.\ see
  \<^item> @{url "http://mathworld.wolfram.com/CantorDiagonalMethod.html"}
  \<^item> @{url "https://en.wikipedia.org/wiki/Cantor's_diagonal_argument"}
\<close>

theorem Cantor: "\<not> (\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A :: 'a set. \<exists>x :: 'a. f x = A)"
proof
  assume "\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. f x = A"
  then obtain f :: "'a \<Rightarrow> 'a set" where *: "\<forall>A. \<exists>x. f x = A" ..
  let ?D = "{x. x \<notin> f x}"
  from * obtain a where "f a = ?D" by blast
  moreover have "a \<in> ?D \<longleftrightarrow> a \<notin> f a" by blast
  ultimately show False by blast
qed


text \<open>
  Here are shorter proofs via automated proof tools, but without any hints why
  and how it works.
\<close>

theorem "\<not> (\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. f x = A)"
  by best

theorem "\<not> (\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. f x = A)"
  by force


subsection \<open>Classic Isabelle/HOL example\<close>

text \<open>
  The following treatment of Cantor's Theorem follows the classic from the
  early 1990s, e.g.\ see the file @{verbatim "92/HOL/ex/set.ML"} in Isabelle92
  or @{cite \<open>\S18.7\<close> "paulson-isa-book"}. The old tactic scripts synthesize
  key information of the proof by refinement of schematic goal states. In
  contrast, the Isar proof needs to say explicitly what is proven.

  \<^bigskip>
  Cantor's Theorem states that every set has more subsets than it has
  elements. It has become a favourite basic example in pure higher-order logic
  since it is so easily expressed:

  @{text [display]
  \<open>\<forall>f::\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool. \<exists>S::\<alpha> \<Rightarrow> bool. \<forall>x::\<alpha>. f x \<noteq> S\<close>}

  Viewing types as sets, \<open>\<alpha> \<Rightarrow> bool\<close> represents the powerset of \<open>\<alpha>\<close>. This
  version of the theorem states that for every function from \<open>\<alpha>\<close> to its
  powerset, some subset is outside its range. The Isabelle/Isar proofs below
  uses HOL's set theory, with the type \<open>\<alpha> set\<close> and the operator \<open>range :: (\<alpha> \<Rightarrow>
  \<beta>) \<Rightarrow> \<beta> set\<close>.
\<close>

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
      with \<open>y \<in> f y\<close> show ?thesis by contradiction
    next
      assume "y \<notin> ?S"
      assume "y \<notin> f y"
      then have "y \<in> ?S" ..
      with \<open>y \<notin> ?S\<close> show ?thesis by contradiction
    qed
  qed
qed

text \<open>
  How much creativity is required? As it happens, Isabelle can prove this
  theorem automatically using best-first search. Depth-first search would
  diverge, but best-first search successfully navigates through the large
  search space. The context of Isabelle's classical prover contains rules for
  the relevant constructs of HOL's set theory.
\<close>

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  by best

end
