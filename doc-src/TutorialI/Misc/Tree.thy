(*<*)
theory Tree = Main:
(*>*)

text{*\noindent
Define the datatype of binary trees
*}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree";(*<*)

consts mirror :: "'a tree \\<Rightarrow> 'a tree";
primrec
"mirror Tip = Tip"
"mirror (Node l x r) = Node (mirror l) x (mirror r)";(*>*)

text{*\noindent
and a function \isa{mirror} that mirrors a binary tree
by swapping subtrees (recursively). Prove
*}

lemma mirror_mirror: "mirror(mirror t) = t";
(*<*)
apply(induct_tac t);
by(auto);

end
(*>*)
