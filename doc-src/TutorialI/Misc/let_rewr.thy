(*<*)
theory let_rewr = Main:;
(*>*)

subsubsection{*Simplifying let-expressions*}

text{*\index{simplification!of let-expressions}
Proving a goal containing \isaindex{let}-expressions almost invariably
requires the @{text"let"}-con\-structs to be expanded at some point. Since
@{text"let"}-@{text"in"} is just syntactic sugar for a predefined constant
(called @{term"Let"}), expanding @{text"let"}-constructs means rewriting with
@{thm[source]Let_def}:
*}

lemma "(let xs = [] in xs@ys@xs) = ys";
by(simp add: Let_def);

text{*
If, in a particular context, there is no danger of a combinatorial explosion
of nested @{text"let"}s one could even add @{thm[source]Let_def} permanently:
*}
lemmas [simp] = Let_def;
(*<*)
end
(*>*)
