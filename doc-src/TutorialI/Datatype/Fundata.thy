(*<*)
theory Fundata = Main:
(*>*)
datatype ('a,'i)bigtree = Tip | Branch 'a "'i \<Rightarrow> ('a,'i)bigtree"

text{*\noindent
Parameter @{typ"'a"} is the type of values stored in
the @{term"Branch"}es of the tree, whereas @{typ"'i"} is the index
type over which the tree branches. If @{typ"'i"} is instantiated to
@{typ"bool"}, the result is a binary tree; if it is instantiated to
@{typ"nat"}, we have an infinitely branching tree because each node
has as many subtrees as there are natural numbers. How can we possibly
write down such a tree? Using functional notation! For example, the term
@{term[display]"Branch 0 (%i. Branch i (%n. Tip))"}
of type @{typ"(nat,nat)bigtree"} is the tree whose
root is labeled with 0 and whose $i$th subtree is labeled with $i$ and
has merely @{term"Tip"}s as further subtrees.

Function @{term"map_bt"} applies a function to all labels in a @{text"bigtree"}:
*}

consts map_bt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'i)bigtree \<Rightarrow> ('b,'i)bigtree"
primrec
"map_bt f Tip          = Tip"
"map_bt f (Branch a F) = Branch (f a) (\<lambda>i. map_bt f (F i))"

text{*\noindent This is a valid \isacommand{primrec} definition because the
recursive calls of @{term"map_bt"} involve only subtrees obtained from
@{term"F"}, i.e.\ the left-hand side. Thus termination is assured.  The
seasoned functional programmer might have written @{term"map_bt f o F"}
instead of @{term"%i. map_bt f (F i)"}, but the former is not accepted by
Isabelle because the termination proof is not as obvious since
@{term"map_bt"} is only partially applied.

The following lemma has a canonical proof  *}

lemma "map_bt (g o f) T = map_bt g (map_bt f T)";
by(induct_tac T, simp_all)

text{*\noindent
%apply(induct_tac T);
%pr(latex xsymbols symbols)
but it is worth taking a look at the proof state after the induction step
to understand what the presence of the function type entails:
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ map{\isacharunderscore}bt\ {\isacharparenleft}g\ {\isasymcirc}\ f{\isacharparenright}\ Tip\ {\isacharequal}\ map{\isacharunderscore}bt\ g\ {\isacharparenleft}map{\isacharunderscore}bt\ f\ Tip{\isacharparenright}\isanewline
\ \isadigit{2}{\isachardot}\ {\isasymAnd}a\ F{\isachardot}\isanewline
\ \ \ \ \ \ \ {\isasymforall}x{\isachardot}\ map{\isacharunderscore}bt\ {\isacharparenleft}g\ {\isasymcirc}\ f{\isacharparenright}\ {\isacharparenleft}F\ x{\isacharparenright}\ {\isacharequal}\ map{\isacharunderscore}bt\ g\ {\isacharparenleft}map{\isacharunderscore}bt\ f\ {\isacharparenleft}F\ x{\isacharparenright}{\isacharparenright}\ {\isasymLongrightarrow}\isanewline
\ \ \ \ \ \ \ map{\isacharunderscore}bt\ {\isacharparenleft}g\ {\isasymcirc}\ f{\isacharparenright}\ {\isacharparenleft}Branch\ a\ F{\isacharparenright}\ {\isacharequal}\ map{\isacharunderscore}bt\ g\ {\isacharparenleft}map{\isacharunderscore}bt\ f\ {\isacharparenleft}Branch\ a\ F{\isacharparenright}{\isacharparenright}
\end{isabelle}
*}
(*<*)
end
(*>*)
