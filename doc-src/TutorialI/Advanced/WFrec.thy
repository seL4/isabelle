(*<*)theory WFrec = Main:(*>*)

text{*\noindent
So far, all recursive definitions where shown to terminate via measure
functions. Sometimes this can be quite inconvenient or even
impossible. Fortunately, \isacommand{recdef} supports much more
general definitions. For example, termination of Ackermann's function
can be shown by means of the lexicographic product @{text"<*lex*>"}:
*}

consts ack :: "nat\<times>nat \<Rightarrow> nat";
recdef ack "measure(\<lambda>m. m) <*lex*> measure(\<lambda>n. n)"
  "ack(0,n)         = Suc n"
  "ack(Suc m,0)     = ack(m, 1)"
  "ack(Suc m,Suc n) = ack(m,ack(Suc m,n))";

text{*\noindent
The lexicographic product decreases if either its first component
decreases (as in the second equation and in the outer call in the
third equation) or its first component stays the same and the second
component decreases (as in the inner call in the third equation).

In general, \isacommand{recdef} supports termination proofs based on
arbitrary well-founded relations as introduced in \S\ref{sec:Well-founded}.
This is called \textbf{well-founded
recursion}\indexbold{recursion!well-founded}\index{well-founded
recursion|see{recursion, well-founded}}. Clearly, a function definition is
total iff the set of all pairs $(r,l)$, where $l$ is the argument on the
left-hand side of an equation and $r$ the argument of some recursive call on
the corresponding right-hand side, induces a well-founded relation.  For a
systematic account of termination proofs via well-founded relations see, for
example, \cite{Baader-Nipkow}.

Each \isacommand{recdef} definition should be accompanied (after the name of
the function) by a well-founded relation on the argument type of the
function.  The HOL library formalizes some of the most important
constructions of well-founded relations (see \S\ref{sec:Well-founded}). For
example, @{term"measure f"} is always well-founded, and the lexicographic
product of two well-founded relations is again well-founded, which we relied
on when defining Ackermann's function above.
Of course the lexicographic product can also be interated:
*}

consts contrived :: "nat \<times> nat \<times> nat \<Rightarrow> nat"
recdef contrived
  "measure(\<lambda>i. i) <*lex*> measure(\<lambda>j. j) <*lex*> measure(\<lambda>k. k)"
"contrived(i,j,Suc k) = contrived(i,j,k)"
"contrived(i,Suc j,0) = contrived(i,j,j)"
"contrived(Suc i,0,0) = contrived(i,i,i)"
"contrived(0,0,0)     = 0"

text{*
Lexicographic products of measure functions already go a long
way. Furthermore you may embedding some type in an
existing well-founded relation via the inverse image construction @{term
inv_image}. All these constructions are known to \isacommand{recdef}. Thus you
will never have to prove well-foundedness of any relation composed
solely of these building blocks. But of course the proof of
termination of your function definition, i.e.\ that the arguments
decrease with every recursive call, may still require you to provide
additional lemmas.

It is also possible to use your own well-founded relations with \isacommand{recdef}.
Here is a simplistic example:
*}

consts f :: "nat \<Rightarrow> nat"
recdef f "id(less_than)"
"f 0 = 0"
"f (Suc n) = f n"

text{*\noindent
Since \isacommand{recdef} is not prepared for @{term id}, the identity
function, this leads to the complaint that it could not prove
@{prop"wf (id less_than)"}.
We should first have proved that @{term id} preserves well-foundedness
*}

lemma wf_id: "wf r \<Longrightarrow> wf(id r)"
by simp;

text{*\noindent
and should have appended the following hint to our above definition:
*}
(*<*)
consts g :: "nat \<Rightarrow> nat"
recdef g "id(less_than)"
"g 0 = 0"
"g (Suc n) = g n"
(*>*)
(hints recdef_wf add: wf_id)
(*<*)end(*>*)
