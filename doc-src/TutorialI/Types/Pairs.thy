(*<*)theory Pairs = Main:(*>*)

section{*Pairs and Tuples*}

text{*\label{sec:products}
Ordered pairs were already introduced in \S\ref{sec:pairs}, but only with a minimal
repertoire of operations: pairing and the two projections @{term fst} and
@{term snd}. In any non-trivial application of pairs you will find that this
quickly leads to unreadable nests of projections. This
section introduces syntactic sugar to overcome this
problem: pattern matching with tuples.
*}

subsection{*Pattern Matching with Tuples*}

text{*
Tuples may be used as patterns in $\lambda$-abstractions,
for example @{text"\<lambda>(x,y,z).x+y+z"} and @{text"\<lambda>((x,y),z).x+y+z"}. In fact,
tuple patterns can be used in most variable binding constructs,
and they can be nested. Here are
some typical examples:
\begin{quote}
@{term"let (x,y) = f z in (y,x)"}\\
@{term"case xs of [] => 0 | (x,y)#zs => x+y"}\\
@{text"\<forall>(x,y)\<in>A. x=y"}\\
@{text"{(x,y,z). x=z}"}\\
@{term"\<Union>(x,y)\<in>A. {x+y}"}
\end{quote}
The intuitive meanings of these expressions should be obvious.
Unfortunately, we need to know in more detail what the notation really stands
for once we have to reason about it.  Abstraction
over pairs and tuples is merely a convenient shorthand for a more complex
internal representation.  Thus the internal and external form of a term may
differ, which can affect proofs. If you want to avoid this complication,
stick to @{term fst} and @{term snd} and write @{term"%p. fst p + snd p"}
instead of @{text"\<lambda>(x,y). x+y"}.  These terms are distinct even though they
denote the same function.

Internally, @{term"%(x,y). t"} becomes @{text"split (\<lambda>x y. t)"}, where
\cdx{split} is the uncurrying function of type @{text"('a \<Rightarrow> 'b
\<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"} defined as
\begin{center}
@{thm split_def}
\hfill(@{thm[source]split_def})
\end{center}
Pattern matching in
other variable binding constructs is translated similarly. Thus we need to
understand how to reason about such constructs.
*}

subsection{*Theorem Proving*}

text{*
The most obvious approach is the brute force expansion of @{term split}:
*}

lemma "(\<lambda>(x,y).x) p = fst p"
by(simp add:split_def)

text{* This works well if rewriting with @{thm[source]split_def} finishes the
proof, as it does above.  But if it does not, you end up with exactly what
we are trying to avoid: nests of @{term fst} and @{term snd}. Thus this
approach is neither elegant nor very practical in large examples, although it
can be effective in small ones.

If we consider why this lemma presents a problem, 
we quickly realize that we need to replace the variable~@{term
p} by some pair @{term"(a,b)"}.  Then both sides of the
equation would simplify to @{term a} by the simplification rules
@{thm split_conv[no_vars]} and @{thm fst_conv[no_vars]}.  
To reason about tuple patterns requires some way of
converting a variable of product type into a pair.

In case of a subterm of the form @{term"split f p"} this is easy: the split
rule @{thm[source]split_split} replaces @{term p} by a pair:%
\index{*split (method)}
*}

lemma "(\<lambda>(x,y).y) p = snd p"
apply(split split_split);

txt{*
@{subgoals[display,indent=0]}
This subgoal is easily proved by simplification. Thus we could have combined
simplification and splitting in one command that proves the goal outright:
*}
(*<*)
by simp
lemma "(\<lambda>(x,y).y) p = snd p"(*>*)
by(simp split: split_split)

text{*
Let us look at a second example:
*}

lemma "let (x,y) = p in fst p = x";
apply(simp only: Let_def)

txt{*
@{subgoals[display,indent=0]}
A paired @{text let} reduces to a paired $\lambda$-abstraction, which
can be split as above. The same is true for paired set comprehension:
*}

(*<*)by(simp split:split_split)(*>*)
lemma "p \<in> {(x,y). x=y} \<longrightarrow> fst p = snd p"
apply simp

txt{*
@{subgoals[display,indent=0]}
Again, simplification produces a term suitable for @{thm[source]split_split}
as above. If you are worried about the strange form of the premise:
@{term"split (op =)"} is short for @{text"\<lambda>(x,y). x=y"}.
The same proof procedure works for
*}

(*<*)by(simp split:split_split)(*>*)
lemma "p \<in> {(x,y). x=y} \<Longrightarrow> fst p = snd p"

txt{*\noindent
except that we now have to use @{thm[source]split_split_asm}, because
@{term split} occurs in the assumptions.

However, splitting @{term split} is not always a solution, as no @{term split}
may be present in the goal. Consider the following function:
*}

(*<*)by(simp split:split_split_asm)(*>*)
consts swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a"
primrec
  "swap (x,y) = (y,x)"

text{*\noindent
Note that the above \isacommand{primrec} definition is admissible
because @{text"\<times>"} is a datatype. When we now try to prove
*}

lemma "swap(swap p) = p"

txt{*\noindent
simplification will do nothing, because the defining equation for @{term swap}
expects a pair. Again, we need to turn @{term p} into a pair first, but this
time there is no @{term split} in sight. In this case the only thing we can do
is to split the term by hand:
*}
apply(case_tac p)

txt{*\noindent
@{subgoals[display,indent=0]}
Again, \methdx{case_tac} is applicable because @{text"\<times>"} is a datatype.
The subgoal is easily proved by @{text simp}.

Splitting by @{text case_tac} also solves the previous examples and may thus
appear preferable to the more arcane methods introduced first. However, see
the warning about @{text case_tac} in \S\ref{sec:struct-ind-case}.

In case the term to be split is a quantified variable, there are more options.
You can split \emph{all} @{text"\<And>"}-quantified variables in a goal
with the rewrite rule @{thm[source]split_paired_all}:
*}

(*<*)by simp(*>*)
lemma "\<And>p q. swap(swap p) = q \<longrightarrow> p = q"
apply(simp only:split_paired_all)

txt{*\noindent
@{subgoals[display,indent=0]}
*}

apply simp
done

text{*\noindent
Note that we have intentionally included only @{thm[source]split_paired_all}
in the first simplification step, and then we simplify again. 
This time the reason was not merely
pedagogical:
@{thm[source]split_paired_all} may interfere with other functions
of the simplifier.
The following command could fail (here it does not)
where two separate \isa{simp} applications succeed.
*}

(*<*)
lemma "\<And>p q. swap(swap p) = q \<longrightarrow> p = q"
(*>*)
apply(simp add:split_paired_all)
(*<*)done(*>*)
text{*\noindent
Finally, the simplifier automatically splits all @{text"\<forall>"} and
@{text"\<exists>"}-quantified variables:
*}

lemma "\<forall>p. \<exists>q. swap p = swap q"
by simp;

text{*\noindent
To turn off this automatic splitting, just disable the
responsible simplification rules:
\begin{center}
@{thm split_paired_All[no_vars]}
\hfill
(@{thm[source]split_paired_All})\\
@{thm split_paired_Ex[no_vars]}
\hfill
(@{thm[source]split_paired_Ex})
\end{center}
*}
(*<*)
end
(*>*)
