(*<*)
theory let_rewr = Main:;
(*>*)
lemma "(let xs = [] in xs@ys@xs) = ys";
apply(simp add: Let_def).;

text{*
If, in a particular context, there is no danger of a combinatorial explosion
of nested \isa{let}s one could even add \isa{Let_def} permanently:
*}
theorems [simp] = Let_def;
(*<*)
end
(*>*)
