(*<*)theory Partial = While_Combinator:(*>*)

text{*\noindent Throughout the tutorial we have emphasized the fact
that all functions in HOL are total. Hence we cannot hope to define
truly partial functions, but must make them total.  A straightforward
method is to lift the result type of the function from $\tau$ to
$\tau$~@{text option} (see \ref{sec:option}), where @{term None} is
returned if the function is applied to an argument not in its
domain. Function @{term assoc} in \S\ref{sec:Trie} is a simple example.
We do not pursue this schema further because it should be clear
how it works. Its main drawback is that the result of such a lifted
function has to be unpacked first before it can be processed
further. Its main advantage is that you can distinguish if the
function was applied to an argument in its domain or not. If you do
not need to make this distinction, for example because the function is
never used outside its domain, it is easier to work with
\emph{underdefined}\index{functions!underdefined} functions: for
certain arguments we only know that a result exists, but we do not
know what it is. When defining functions that are normally considered
partial, underdefinedness turns out to be a very reasonable
alternative.

We have already seen an instance of underdefinedness by means of
non-exhaustive pattern matching: the definition of @{term last} in
\S\ref{sec:recdef-examples}. The same is allowed for \isacommand{primrec}
*}

consts hd :: "'a list \<Rightarrow> 'a"
primrec "hd (x#xs) = x"

text{*\noindent
although it generates a warning.
Even ordinary definitions allow underdefinedness, this time by means of
preconditions:
*}

constdefs minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
"n \<le> m \<Longrightarrow> minus m n \<equiv> m - n"

text{*
The rest of this section is devoted to the question of how to define
partial recursive functions by other means than non-exhaustive pattern
matching.
*}

subsubsection{*Guarded Recursion*}

text{* Neither \isacommand{primrec} nor \isacommand{recdef} allow to
prefix an equation with a condition in the way ordinary definitions do
(see @{term minus} above). Instead we have to move the condition over
to the right-hand side of the equation. Given a partial function $f$
that should satisfy the recursion equation $f(x) = t$ over its domain
$dom(f)$, we turn this into the \isacommand{recdef}
@{prop[display]"f(x) = (if x \<in> dom(f) then t else arbitrary)"}
where @{term arbitrary} is a predeclared constant of type @{typ 'a}
which has no definition. Thus we know nothing about its value,
which is ideal for specifying underdefined functions on top of it.

As a simple example we define division on @{typ nat}:
*}

consts divi :: "nat \<times> nat \<Rightarrow> nat"
recdef divi "measure(\<lambda>(m,n). m)"
  "divi(m,n) = (if n = 0 then arbitrary else
                if m < n then 0 else divi(m-n,n)+1)"

text{*\noindent Of course we could also have defined
@{term"divi(m,0)"} to be some specific number, for example 0. The
latter option is chosen for the predefined @{text div} function, which
simplifies proofs at the expense of deviating from the
standard mathematical division function.

As a more substantial example we consider the problem of searching a graph.
For simplicity our graph is given by a function @{term f} of
type @{typ"'a \<Rightarrow> 'a"} which
maps each node to its successor, i.e.\ the graph is really a tree.
The task is to find the end of a chain, modelled by a node pointing to
itself. Here is a first attempt:
@{prop[display]"find(f,x) = (if f x = x then x else find(f, f x))"}
This may be viewed as a fixed point finder or as one half of the well known
\emph{Union-Find} algorithm.
The snag is that it may not terminate if @{term f} has non-trivial cycles.
Phrased differently, the relation
*}

constdefs step1 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'a)set"
  "step1 f \<equiv> {(y,x). y = f x \<and> y \<noteq> x}"

text{*\noindent
must be well-founded. Thus we make the following definition:
*}

consts find :: "('a \<Rightarrow> 'a) \<times> 'a \<Rightarrow> 'a"
recdef find "same_fst (\<lambda>f. wf(step1 f)) step1"
  "find(f,x) = (if wf(step1 f)
                then if f x = x then x else find(f, f x)
                else arbitrary)"
(hints recdef_simp: step1_def)

text{*\noindent
The recursion equation itself should be clear enough: it is our aborted
first attempt augmented with a check that there are no non-trivial loops.
To express the required well-founded relation we employ the
predefined combinator @{term same_fst} of type
@{text[display]"('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('b\<times>'b)set) \<Rightarrow> (('a\<times>'b) \<times> ('a\<times>'b))set"}
defined as
@{thm[display]same_fst_def[no_vars]}
This combinator is designed for
recursive functions on pairs where the first component of the argument is
passed unchanged to all recursive calls. Given a constraint on the first
component and a relation on the second component, @{term same_fst} builds the
required relation on pairs.  The theorem
@{thm[display]wf_same_fst[no_vars]}
is known to the well-foundedness prover of \isacommand{recdef}.  Thus
well-foundedness of the relation given to \isacommand{recdef} is immediate.
Furthermore, each recursive call descends along that relation: the first
argument stays unchanged and the second one descends along @{term"step1
f"}. The proof requires unfolding the definition of @{term step1},
as specified in the \isacommand{hints} above.

Normally you will then derive the following conditional variant of and from
the recursion equation
*}

lemma [simp]:
  "wf(step1 f) \<Longrightarrow> find(f,x) = (if f x = x then x else find(f, f x))"
by simp

text{*\noindent and then disable the original recursion equation:*}

declare find.simps[simp del]

text{*
We can reason about such underdefined functions just like about any other
recursive function. Here is a simple example of recursion induction:
*}

lemma "wf(step1 f) \<longrightarrow> f(find(f,x)) = find(f,x)"
apply(induct_tac f x rule:find.induct);
apply simp
done

subsubsection{*The {\tt\slshape while} Combinator*}

text{*If the recursive function happens to be tail recursive, its
definition becomes a triviality if based on the predefined \cdx{while}
combinator.  The latter lives in the Library theory
\thydx{While_Combinator}, which is not part of @{text Main} but needs to
be included explicitly among the ancestor theories.

Constant @{term while} is of type @{text"('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"}
and satisfies the recursion equation @{thm[display]while_unfold[no_vars]}
That is, @{term"while b c s"} is equivalent to the imperative program
\begin{verbatim}
     x := s; while b(x) do x := c(x); return x
\end{verbatim}
In general, @{term s} will be a tuple (better still: a record). As an example
consider the following definition of function @{term find} above:
*}

constdefs find2 :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  "find2 f x \<equiv>
   fst(while (\<lambda>(x,x'). x' \<noteq> x) (\<lambda>(x,x'). (x',f x')) (x,f x))"

text{*\noindent
The loop operates on two ``local variables'' @{term x} and @{term x'}
containing the ``current'' and the ``next'' value of function @{term f}.
They are initialized with the global @{term x} and @{term"f x"}. At the
end @{term fst} selects the local @{term x}.

Although the definition of tail recursive functions via @{term while} avoids
termination proofs, there is no free lunch. When proving properties of
functions defined by @{term while}, termination rears its ugly head
again. Here is @{thm[source]while_rule}, the well known proof rule for total
correctness of loops expressed with @{term while}:
@{thm[display,margin=50]while_rule[no_vars]} @{term P} needs to be true of
the initial state @{term s} and invariant under @{term c} (premises 1
and~2). The post-condition @{term Q} must become true when leaving the loop
(premise~3). And each loop iteration must descend along a well-founded
relation @{term r} (premises 4 and~5).

Let us now prove that @{term find2} does indeed find a fixed point. Instead
of induction we apply the above while rule, suitably instantiated.
Only the final premise of @{thm[source]while_rule} is left unproved
by @{text auto} but falls to @{text simp}:
*}

lemma lem: "wf(step1 f) \<Longrightarrow>
  \<exists>y. while (\<lambda>(x,x'). x' \<noteq> x) (\<lambda>(x,x'). (x',f x')) (x,f x) = (y,y) \<and>
       f y = y"
apply(rule_tac P = "\<lambda>(x,x'). x' = f x" and
               r = "inv_image (step1 f) fst" in while_rule);
apply auto
apply(simp add:inv_image_def step1_def)
done

text{*
The theorem itself is a simple consequence of this lemma:
*}

theorem "wf(step1 f) \<Longrightarrow> f(find2 f x) = find2 f x"
apply(drule_tac x = x in lem)
apply(auto simp add:find2_def)
done

text{* Let us conclude this section on partial functions by a
discussion of the merits of the @{term while} combinator. We have
already seen that the advantage (if it is one) of not having to
provide a termination argument when defining a function via @{term
while} merely puts off the evil hour. On top of that, tail recursive
functions tend to be more complicated to reason about. So why use
@{term while} at all? The only reason is executability: the recursion
equation for @{term while} is a directly executable functional
program. This is in stark contrast to guarded recursion as introduced
above which requires an explicit test @{prop"x \<in> dom f"} in the
function body.  Unless @{term dom} is trivial, this leads to a
definition that is impossible to execute or prohibitively slow.
Thus, if you are aiming for an efficiently executable definition
of a partial function, you are likely to need @{term while}.
*}

(*<*)end(*>*)
