theory FP0 = PreList:

datatype 'a list = Nil                          ("[]")
                 | Cons 'a "'a list"            (infixr "#" 65)

consts app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"   (infixr "@" 65)
       rev :: "'a list \<Rightarrow> 'a list"

primrec
"[] @ ys       = ys"
"(x # xs) @ ys = x # (xs @ ys)"

primrec
"rev []        = []"
"rev (x # xs)  = (rev xs) @ (x # [])"

theorem rev_rev [simp]: "rev(rev xs) = xs"
(*<*)oops(*>*)


text{*
\begin{exercise}
Define a datatype of binary trees and a function @{term mirror}
that mirrors a binary tree by swapping subtrees recursively. Prove
@{prop"mirror(mirror t) = t"}.

Define a function @{term flatten} that flattens a tree into a list
by traversing it in infix order. Prove
@{prop"flatten(mirror t) = rev(flatten t)"}.
\end{exercise}
*}

end
