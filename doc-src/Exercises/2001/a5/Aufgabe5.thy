(*<*)
theory Aufgabe5 = Main:
(*>*)

subsection {* Interval lists *}


text {* Sets of natural numbers can be implemented as lists of
intervals, where an interval is simply a pair of numbers. For example
the set @{term "{2, 3, 5, 7, 8, 9::nat}"} can be represented by the
list @{term "[(2, 3), (5, 5), (7::nat,9::nat)]"}. A typical application
is the list of free blocks of dynamically allocated memory. *}

subsubsection {* Definitions *} 

text {* We introduce the type *}

types intervals = "(nat*nat) list" 

text {* This type contains all possible lists of pairs of natural
numbers, even those that we may not recognize as meaningful
representations of sets. Thus you should introduce an \emph{invariant} *}

consts inv :: "intervals => bool"

text {* that characterizes exactly those interval lists representing
sets.  (The reason why we call this an invariant will become clear
below.)  For efficiency reasons intervals should be sorted in
ascending order, the lower bound of each interval should be less or
equal the upper bound, and the intervals should be chosen as large as
possible, i.e.\ no two adjecent intervals should overlap or even touch
each other.  It turns out to be convenient to define @{term inv} in
terms of a more general function *}

consts inv2 :: "nat => intervals => bool"

text {* such that the additional argument is a lower bound for the
intervals in the list.

To relate intervals back to sets define an \emph{abstraktion funktion}  *} 

consts set_of :: "intervals => nat set"

text {* that yields the set corresponding to an interval list (that
satisfies the invariant).

Finally, define two primitive recursive functions
*}

consts add :: "(nat*nat) => intervals => intervals"
       rem :: "(nat*nat) => intervals => intervals"

text {* for inserting and deleting an interval from an interval
list. The result should again satisfies the invariant. Hence the name:
@{text inv} is invariant under the application of the operations
@{term add} and @{term rem} --- if @{text inv} holds for the input, it
must also hold for the output.
*}

subsubsection {* Proving the invariant *}

declare Let_def [simp]
declare split_split [split]

text {* Start off by proving the monotonicity of @{term inv2}: *}

lemma inv2_monotone: "inv2 m ins \<Longrightarrow> n\<le>m \<Longrightarrow> inv2 n ins"
(*<*)oops(*>*)

text {*
Now show that @{term add} and @{term rem} preserve the invariant:
*}

theorem inv_add: "\<lbrakk> i\<le>j; inv ins \<rbrakk> \<Longrightarrow> inv (add (i,j) ins)"
(*<*)oops(*>*)

theorem inv_rem: "\<lbrakk> i\<le>j; inv ins \<rbrakk> \<Longrightarrow> inv (rem (i,j) ins)"
(*<*)oops(*>*)

text {* Hint: you should first prove a more general statement
(involving @{term inv2}). This will probably involve some advanced
forms of induction discussed in section~9.3.1 of
\cite{isabelle-tutorial}.  *}


subsubsection {* Proving correctness of the implementation *}

text {* Show the correctness of @{term add} and @{term rem} wrt.\
their counterparts @{text"\<union>"} and @{text"-"} on sets: *}

theorem set_of_add: 
  "\<lbrakk> i\<le>j; inv ins \<rbrakk> \<Longrightarrow> set_of (add (i,j) ins) = set_of [(i,j)] \<union> set_of ins"
(*<*)oops(*>*)

theorem set_of_rem:
  "\<lbrakk> i \<le> j; inv ins \<rbrakk> \<Longrightarrow> set_of (rem (i,j) ins) = set_of ins - set_of [(i,j)]"
(*<*)oops(*>*)

text {* Hints: in addition to the hints above, you may also find it
useful to prove some relationship between @{term inv2} and @{term
set_of} as a lemma.  *}

subsubsection{* General hints *}

text {* 
\begin{itemize}

\item You should be familiar both with simplification and predicate
calculus reasoning. Automatic tactics like @{text blast} and @{text
force} can simplify the proof.

\item
Equality of two sets can often be proved via the rule @{text set_ext}:
@{thm[display] set_ext[of A B,no_vars]}

\item 
Potentially useful theorems for the simplification of sets include \\
@{text "Un_Diff:"}~@{thm Un_Diff [no_vars]} \\
@{text "Diff_triv:"}~@{thm Diff_triv [no_vars]}.

\item 
Theorems can be instantiated and simplified via @{text of} and
@{text "[simplified]"} (see \cite{isabelle-tutorial}).
\end{itemize}
*}(*<*)
end
(*>*)
