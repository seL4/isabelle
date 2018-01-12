(*<*)
theory Tree imports Main begin
(*>*)

text\<open>\noindent
Define the datatype of \rmindex{binary trees}:
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"(*<*)

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"(*>*)

text\<open>\noindent
Define a function @{term"mirror"} that mirrors a binary tree
by swapping subtrees recursively. Prove
\<close>

lemma mirror_mirror: "mirror(mirror t) = t"
(*<*)
apply(induct_tac t)
by(auto)

primrec flatten :: "'a tree => 'a list" where
"flatten Tip = []" |
"flatten (Node l x r) = flatten l @ [x] @ flatten r"
(*>*)

text\<open>\noindent
Define a function @{term"flatten"} that flattens a tree into a list
by traversing it in infix order. Prove
\<close>

lemma "flatten(mirror t) = rev(flatten t)"
(*<*)
apply(induct_tac t)
by(auto)

end
(*>*)
