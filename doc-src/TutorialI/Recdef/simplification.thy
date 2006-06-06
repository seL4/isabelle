(*<*)
theory simplification imports Main begin;
(*>*)

text{*
Once we have proved all the termination conditions, the \isacommand{recdef} 
recursion equations become simplification rules, just as with
\isacommand{primrec}. In most cases this works fine, but there is a subtle
problem that must be mentioned: simplification may not
terminate because of automatic splitting of @{text "if"}.
\index{*if expressions!splitting of}
Let us look at an example:
*}

consts gcd :: "nat\<times>nat \<Rightarrow> nat";
recdef gcd "measure (\<lambda>(m,n).n)"
  "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))";

text{*\noindent
According to the measure function, the second argument should decrease with
each recursive call. The resulting termination condition
@{term[display]"n ~= (0::nat) ==> m mod n < n"}
is proved automatically because it is already present as a lemma in
HOL\@.  Thus the recursion equation becomes a simplification
rule. Of course the equation is nonterminating if we are allowed to unfold
the recursive call inside the @{text else} branch, which is why programming
languages and our simplifier don't do that. Unfortunately the simplifier does
something else that leads to the same problem: it splits 
each @{text "if"}-expression unless its
condition simplifies to @{term True} or @{term False}.  For
example, simplification reduces
@{term[display]"gcd(m,n) = k"}
in one step to
@{term[display]"(if n=0 then m else gcd(n, m mod n)) = k"}
where the condition cannot be reduced further, and splitting leads to
@{term[display]"(n=0 --> m=k) & (n ~= 0 --> gcd(n, m mod n)=k)"}
Since the recursive call @{term"gcd(n, m mod n)"} is no longer protected by
an @{text "if"}, it is unfolded again, which leads to an infinite chain of
simplification steps. Fortunately, this problem can be avoided in many
different ways.

The most radical solution is to disable the offending theorem
@{thm[source]split_if},
as shown in \S\ref{sec:AutoCaseSplits}.  However, we do not recommend this
approach: you will often have to invoke the rule explicitly when
@{text "if"} is involved.

If possible, the definition should be given by pattern matching on the left
rather than @{text "if"} on the right. In the case of @{term gcd} the
following alternative definition suggests itself:
*}

consts gcd1 :: "nat\<times>nat \<Rightarrow> nat";
recdef gcd1 "measure (\<lambda>(m,n).n)"
  "gcd1 (m, 0) = m"
  "gcd1 (m, n) = gcd1(n, m mod n)";


text{*\noindent
The order of equations is important: it hides the side condition
@{prop"n ~= (0::nat)"}.  Unfortunately, in general the case distinction
may not be expressible by pattern matching.

A simple alternative is to replace @{text "if"} by @{text case}, 
which is also available for @{typ bool} and is not split automatically:
*}

consts gcd2 :: "nat\<times>nat \<Rightarrow> nat";
recdef gcd2 "measure (\<lambda>(m,n).n)"
  "gcd2(m,n) = (case n=0 of True \<Rightarrow> m | False \<Rightarrow> gcd2(n,m mod n))";

text{*\noindent
This is probably the neatest solution next to pattern matching, and it is
always available.

A final alternative is to replace the offending simplification rules by
derived conditional ones. For @{term gcd} it means we have to prove
these lemmas:
*}

lemma [simp]: "gcd (m, 0) = m";
apply(simp);
done

lemma [simp]: "n \<noteq> 0 \<Longrightarrow> gcd(m, n) = gcd(n, m mod n)";
apply(simp);
done

text{*\noindent
Simplification terminates for these proofs because the condition of the @{text
"if"} simplifies to @{term True} or @{term False}.
Now we can disable the original simplification rule:
*}

declare gcd.simps [simp del]

(*<*)
end
(*>*)
