(*<*)
theory Tree2 = Tree:
(*>*)

text{*\noindent In Exercise~\ref{ex:Tree} we defined a function
\isa{flatten} from trees to lists. The straightforward version of
\isa{flatten} is based on \isa{\at} and is thus, like \isa{rev}, quadratic.
A linear time version of \isa{flatten} again reqires an extra
argument, the accumulator: *}

consts flatten2 :: "'a tree => 'a list => 'a list"
(*<*)
primrec
"flatten2 Tip xs = xs"
"flatten2 (Node l x r) xs = flatten2 l (x#(flatten2 r xs))"
(*>*)

text{*\noindent Define \isa{flatten2} and prove
*}
(*<*)
lemma [simp]: "!xs. flatten2 t xs = flatten t @ xs";
apply(induct_tac t);
by(auto);
(*>*)
lemma "flatten2 t [] = flatten t";
(*<*)
by(simp);

end
(*>*)
