(*<*)
theory simplification = Main:;
(*>*)

text{*
Once we have succeeded in proving all termination conditions, the recursion
equations become simplification rules, just as with
\isacommand{primrec}. In most cases this works fine, but there is a subtle
problem that must be mentioned: simplification may not
terminate because of automatic splitting of \isa{if}.
Let us look at an example:
*}

consts gcd :: "nat*nat \\<Rightarrow> nat";
recdef gcd "measure (\\<lambda>(m,n).n)"
  "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))";

text{*\noindent
According to the measure function, the second argument should decrease with
each recursive call. The resulting termination condition
*}

(*<*)term(*>*) "n \\<noteq> 0 \\<Longrightarrow> m mod n < n";

text{*\noindent
is provded automatically because it is already present as a lemma in the
arithmetic library. Thus the recursion equation becomes a simplification
rule. Of course the equation is nonterminating if we are allowed to unfold
the recursive call inside the \isa{else} branch, which is why programming
languages and our simplifier don't do that. Unfortunately the simplifier does
something else which leads to the same problem: it splits \isa{if}s if the
condition simplifies to neither \isa{True} nor \isa{False}. For
example, simplification reduces
*}

(*<*)term(*>*) "gcd(m,n) = k";

text{*\noindent
in one step to
*}

(*<*)term(*>*) "(if n=0 then m else gcd(n, m mod n)) = k";

text{*\noindent
where the condition cannot be reduced further, and splitting leads to
*}

(*<*)term(*>*) "(n=0 \\<longrightarrow> m=k) \\<and> (n\\<noteq>0 \\<longrightarrow> gcd(n, m mod n)=k)";

text{*\noindent
Since the recursive call \isa{gcd(n, m mod n)} is no longer protected by
an \isa{if}, this leads to an infinite chain of simplification steps.
Fortunately, this problem can be avoided in many different ways.

Of course the most radical solution is to disable the offending
\isa{split_if} as shown in the section on case splits in
\S\ref{sec:SimpFeatures}.
However, we do not recommend this because it means you will often have to
invoke the rule explicitly when \isa{if} is involved.

If possible, the definition should be given by pattern matching on the left
rather than \isa{if} on the right. In the case of \isa{gcd} the
following alternative definition suggests itself:
*}

consts gcd1 :: "nat*nat \\<Rightarrow> nat";
recdef gcd1 "measure (\\<lambda>(m,n).n)"
  "gcd1 (m, 0) = m"
  "gcd1 (m, n) = gcd1(n, m mod n)";


text{*\noindent
Note that the order of equations is important and hides the side condition
\isa{n \isasymnoteq\ 0}. Unfortunately, in general the case distinction
may not be expressible by pattern matching.

A very simple alternative is to replace \isa{if} by \isa{case}, which
is also available for \isa{bool} but is not split automatically:
*}

consts gcd2 :: "nat*nat \\<Rightarrow> nat";
recdef gcd2 "measure (\\<lambda>(m,n).n)"
  "gcd2(m,n) = (case n=0 of True \\<Rightarrow> m | False \\<Rightarrow> gcd2(n,m mod n))";

text{*\noindent
In fact, this is probably the neatest solution next to pattern matching.

A final alternative is to replace the offending simplification rules by
derived conditional ones. For \isa{gcd} it means we have to prove
*}

lemma [simp]: "gcd (m, 0) = m";
apply(simp).;
lemma [simp]: "n \\<noteq> 0 \\<Longrightarrow> gcd(m, n) = gcd(n, m mod n)";
apply(simp).;

text{*\noindent
after which we can disable the original simplification rule:
*}

lemmas [simp del] = gcd.simps;

(*<*)
end
(*>*)
