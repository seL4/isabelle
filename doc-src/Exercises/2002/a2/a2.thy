(*<*)
theory a2 = Main:
(*>*)
subsection {* Sorting \label{psv2002a2} *}

text{* For simplicity we sort natural numbers. *}

subsubsection{* Sorting with lists*}

text {*
The task is to define insertion sort and prove its correctness.
The following functions are required:
*}

consts 
  insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  sort   :: "nat list \<Rightarrow> nat list"
  le     :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  sorted :: "nat list \<Rightarrow> bool"

text {* In your definition, @{term "insort x xs"} should insert a
number @{term x} into an already sorted list @{text xs}, and @{term
"sort ys"} should build on @{text insort} to produce the sorted
version of @{text ys}.

To show that the resulting list is indeed sorted we need a predicate
@{term sorted} that checks if each element in the list is less or equal
to the following ones; @{term "le n xs"} should be true iff
@{term n} is less or equal to all elements of @{text xs}.

Start out by showing a monotonicity property of @{term le}.
For technical reasons the lemma should be phrased as follows:
*}
lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
(*<*)oops(*>*)

text {* Now show the following correctness theorem: *}
theorem "sorted (sort xs)"
(*<*)oops(*>*)

text {* This theorem alone is too weak. It does not guarantee that the
sorted list contains the same elements as the input. In the worst
case, @{term sort} might always return @{term"[]"} --- surely an
undesirable implementation of sorting.

Define a function @{term "count xs x"} that counts how often @{term x}
occurs in @{term xs}. Show that
*}

theorem "count (sort xs) x = count xs x"
(*<*)oops(*>*)

subsubsection {* Sorting with trees *}

text {* Our second sorting algorithm uses trees. Thus you should first
define a data type @{text bintree} of binary trees that are either
empty or consist of a node carrying a natural number and two subtrees.

Define a function @{text tsorted} that checks if a binary tree is
sorted. It is convenien to employ two auxiliary functions @{text
tge}/@{text tle} that test whether a number is
greater-or-equal/less-or-equal to all elements of a tree.

Finally define a function @{text tree_of} that turns a list into a
sorted tree. It is helpful to base @{text tree_of} on a function
@{term "ins n b"} that inserts a number @{term n} into a sorted tree
@{term b}.

Show
*}
theorem [simp]: "tsorted (tree_of xs)"
(*<*)oops(*>*)

text {* Again we have to show that no elements are lost (or added).
As for lists, define a function @{term "tcount x b"} that counts the
number of occurrences of the number @{term x} in the tree @{term b}.
Show
*}

theorem "tcount (tree_of xs) x = count xs x"
(*<*)oops(*>*)

text {* Now we are ready to sort lists. We know how to produce an
ordered tree from a list. Thus we merely need a function @{text
list_of} that turns an (ordered) tree into an (ordered) list.
Define this function and prove
*}

theorem "sorted (list_of (tree_of xs))"
(*<*)oops(*>*)

theorem "count (list_of (tree_of xs)) n = count xs n"    
(*<*)oops(*>*)

text {*
Hints:
\begin{itemize}
\item
Try to formulate all your lemmas as equations rather than implications
because that often simplifies their proof.
Make sure that the right-hand side is (in some sense)
simpler than the left-hand side.
\item
Eventually you need to relate @{text sorted} and @{text tsorted}.
This is facilitated by a function @{text ge} on lists (analogously to
@{text tge} on trees) and the following lemma (that you will need to prove):
@{term[display] "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a \<and> le x b)"}
\end{itemize}
*}

(*<*)
end
(*>*)