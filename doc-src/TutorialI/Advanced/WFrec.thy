(*<*)theory WFrec = Main:(*>*)

text{*\noindent
So far, all recursive definitions were shown to terminate via measure
functions. Sometimes this can be inconvenient or
impossible. Fortunately, \isacommand{recdef} supports much more
general definitions. For example, termination of Ackermann's function
can be shown by means of the \rmindex{lexicographic product} @{text"<*lex*>"}:
*}

consts ack :: "nat\<times>nat \<Rightarrow> nat"
recdef ack "measure(\<lambda>m. m) <*lex*> measure(\<lambda>n. n)"
  "ack(0,n)         = Suc n"
  "ack(Suc m,0)     = ack(m, 1)"
  "ack(Suc m,Suc n) = ack(m,ack(Suc m,n))"

text{*\noindent
The lexicographic product decreases if either its first component
decreases (as in the second equation and in the outer call in the
third equation) or its first component stays the same and the second
component decreases (as in the inner call in the third equation).

In general, \isacommand{recdef} supports termination proofs based on
arbitrary well-founded relations as introduced in \S\ref{sec:Well-founded}.
This is called \textbf{well-founded
recursion}\indexbold{recursion!well-founded}.  A function definition
is total if and only if the set of 
all pairs $(r,l)$, where $l$ is the argument on the
left-hand side of an equation and $r$ the argument of some recursive call on
the corresponding right-hand side, induces a well-founded relation.  For a
systematic account of termination proofs via well-founded relations see, for
example, Baader and Nipkow~\cite{Baader-Nipkow}.

Each \isacommand{recdef} definition should be accompanied (after the function's
name) by a well-founded relation on the function's argument type.  
Isabelle/HOL formalizes some of the most important
constructions of well-founded relations (see \S\ref{sec:Well-founded}). For
example, @{term"measure f"} is always well-founded.   The lexicographic
product of two well-founded relations is again well-founded, which we relied
on when defining Ackermann's function above.
Of course the lexicographic product can also be iterated:
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
way. Furthermore, you may embed a type in an
existing well-founded relation via the inverse image construction @{term
inv_image}. All these constructions are known to \isacommand{recdef}. Thus you
will never have to prove well-foundedness of any relation composed
solely of these building blocks. But of course the proof of
termination of your function definition --- that the arguments
decrease with every recursive call --- may still require you to provide
additional lemmas.

It is also possible to use your own well-founded relations with
\isacommand{recdef}.  For example, the greater-than relation can be made
well-founded by cutting it off at a certain point.  Here is an example
of a recursive function that calls itself with increasing values up to ten:
*}

consts f :: "nat \<Rightarrow> nat"
recdef (*<*)(permissive)(*>*)f "{(i,j). j<i \<and> i \<le> (10::nat)}"
"f i = (if 10 \<le> i then 0 else i * f(Suc i))"

text{*\noindent
Since \isacommand{recdef} is not prepared for the relation supplied above,
Isabelle rejects the definition.  We should first have proved that
our relation was well-founded:
*}

lemma wf_greater: "wf {(i,j). j<i \<and> i \<le> (N::nat)}"

txt{*\noindent
The proof is by showing that our relation is a subset of another well-founded
relation: one given by a measure function.\index{*wf_subset (theorem)}
*}

apply (rule wf_subset [of "measure (\<lambda>k::nat. N-k)"], blast)

txt{*
@{subgoals[display,indent=0,margin=65]}

\noindent
The inclusion remains to be proved. After unfolding some definitions, 
we are left with simple arithmetic:
*}

apply (clarify, simp add: measure_def inv_image_def)

txt{*
@{subgoals[display,indent=0,margin=65]}

\noindent
And that is dispatched automatically:
*}

by arith

text{*\noindent

Armed with this lemma, we use the \attrdx{recdef_wf} attribute to attach a
crucial hint to our definition:
*}
(*<*)
consts g :: "nat \<Rightarrow> nat"
recdef g "{(i,j). j<i \<and> i \<le> (10::nat)}"
"g i = (if 10 \<le> i then 0 else i * g(Suc i))"
(*>*)
(hints recdef_wf: wf_greater)

text{*\noindent
Alternatively, we could have given @{text "measure (\<lambda>k::nat. 10-k)"} for the
well-founded relation in our \isacommand{recdef}.  However, the arithmetic
goal in the lemma above would have arisen instead in the \isacommand{recdef}
termination proof, where we have less control.  A tailor-made termination
relation makes even more sense when it can be used in several function
declarations.
*}

(*<*)end(*>*)
