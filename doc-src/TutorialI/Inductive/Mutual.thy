(*<*)theory Mutual = Main:(*>*)

subsection{*Mutually Inductive Definitions*}

text{*
Just as there are datatypes defined by mutual recursion, there are sets defined
by mutual induction. As a trivial example we consider the even and odd
natural numbers:
*}

consts even :: "nat set"
       odd  :: "nat set"

inductive even odd
intros
zero:  "0 \<in> even"
evenI: "n \<in> odd \<Longrightarrow> Suc n \<in> even"
oddI:  "n \<in> even \<Longrightarrow> Suc n \<in> odd"

text{*\noindent
The mutually inductive definition of multiple sets is no different from
that of a single set, except for induction: just as for mutually recursive
datatypes, induction needs to involve all the simultaneously defined sets. In
the above case, the induction rule is called @{thm[source]even_odd.induct}
(simply concatenate the names of the sets involved) and has the conclusion
@{text[display]"(?x \<in> even \<longrightarrow> ?P ?x) \<and> (?y \<in> odd \<longrightarrow> ?Q ?y)"}

If we want to prove that all even numbers are divisible by two, we have to
generalize the statement as follows:
*}

lemma "(m \<in> even \<longrightarrow> 2 dvd m) \<and> (n \<in> odd \<longrightarrow> 2 dvd (Suc n))"

txt{*\noindent
The proof is by rule induction. Because of the form of the induction theorem,
it is applied by @{text rule} rather than @{text erule} as for ordinary
inductive definitions:
*}

apply(rule even_odd.induct)

txt{*
@{subgoals[display,indent=0]}
The first two subgoals are proved by simplification and the final one can be
proved in the same manner as in \S\ref{sec:rule-induction}
where the same subgoal was encountered before.
We do not show the proof script.
*}
(*<*)
  apply simp
 apply simp
apply(simp add: dvd_def)
apply(clarify)
apply(rule_tac x = "Suc k" in exI)
apply simp
done
(*>*)
(*
Exercise: 1 : odd
*)
(*<*)end(*>*)
