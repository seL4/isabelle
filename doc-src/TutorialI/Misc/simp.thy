(*<*)
theory simp = Main:
(*>*)

subsubsection{*Simplification rules*}

text{*\indexbold{simplification rule}
To facilitate simplification, theorems can be declared to be simplification
rules (with the help of the attribute @{text"[simp]"}\index{*simp
  (attribute)}), in which case proofs by simplification make use of these
rules automatically. In addition the constructs \isacommand{datatype} and
\isacommand{primrec} (and a few others) invisibly declare useful
simplification rules. Explicit definitions are \emph{not} declared
simplification rules automatically!

Not merely equations but pretty much any theorem can become a simplification
rule. The simplifier will try to make sense of it.  For example, a theorem
@{prop"~P"} is automatically turned into @{prop"P = False"}. The details
are explained in \S\ref{sec:SimpHow}.

The simplification attribute of theorems can be turned on and off as follows:
\begin{quote}
\isacommand{declare} \textit{theorem-name}@{text"[simp]"}\\
\isacommand{declare} \textit{theorem-name}@{text"[simp del]"}
\end{quote}
As a rule of thumb, equations that really simplify (like @{prop"rev(rev xs) =
 xs"} and @{prop"xs @ [] = xs"}) should be made simplification
rules.  Those of a more specific nature (e.g.\ distributivity laws, which
alter the structure of terms considerably) should only be used selectively,
i.e.\ they should not be default simplification rules.  Conversely, it may
also happen that a simplification rule needs to be disabled in certain
proofs.  Frequent changes in the simplification status of a theorem may
indicate a badly designed theory.
\begin{warn}
  Simplification may not terminate, for example if both $f(x) = g(x)$ and
  $g(x) = f(x)$ are simplification rules. It is the user's responsibility not
  to include simplification rules that can lead to nontermination, either on
  their own or in combination with other simplification rules.
\end{warn}
*}

subsubsection{*The simplification method*}

text{*\index{*simp (method)|bold}
The general format of the simplification method is
\begin{quote}
@{text simp} \textit{list of modifiers}
\end{quote}
where the list of \emph{modifiers} helps to fine tune the behaviour and may
be empty. Most if not all of the proofs seen so far could have been performed
with @{text simp} instead of \isa{auto}, except that @{text simp} attacks
only the first subgoal and may thus need to be repeated---use
\isaindex{simp_all} to simplify all subgoals.
Note that @{text simp} fails if nothing changes.
*}

subsubsection{*Adding and deleting simplification rules*}

text{*
If a certain theorem is merely needed in a few proofs by simplification,
we do not need to make it a global simplification rule. Instead we can modify
the set of simplification rules used in a simplification step by adding rules
to it and/or deleting rules from it. The two modifiers for this are
\begin{quote}
@{text"add:"} \textit{list of theorem names}\\
@{text"del:"} \textit{list of theorem names}
\end{quote}
In case you want to use only a specific list of theorems and ignore all
others:
\begin{quote}
@{text"only:"} \textit{list of theorem names}
\end{quote}
*}

subsubsection{*Assumptions*}

text{*\index{simplification!with/of assumptions}
By default, assumptions are part of the simplification process: they are used
as simplification rules and are simplified themselves. For example:
*}

lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs";
apply simp;
done

text{*\noindent
The second assumption simplifies to @{term"xs = []"}, which in turn
simplifies the first assumption to @{term"zs = ys"}, thus reducing the
conclusion to @{term"ys = ys"} and hence to @{term"True"}.

In some cases this may be too much of a good thing and may lead to
nontermination:
*}

lemma "\<forall>x. f x = g (f (g x)) \<Longrightarrow> f [] = f [] @ []";

txt{*\noindent
cannot be solved by an unmodified application of @{text"simp"} because the
simplification rule @{term"f x = g (f (g x))"} extracted from the assumption
does not terminate. Isabelle notices certain simple forms of
nontermination but not this one. The problem can be circumvented by
explicitly telling the simplifier to ignore the assumptions:
*}

apply(simp (no_asm));
done

text{*\noindent
There are three options that influence the treatment of assumptions:
\begin{description}
\item[@{text"(no_asm)"}]\indexbold{*no_asm}
 means that assumptions are completely ignored.
\item[@{text"(no_asm_simp)"}]\indexbold{*no_asm_simp}
 means that the assumptions are not simplified but
  are used in the simplification of the conclusion.
\item[@{text"(no_asm_use)"}]\indexbold{*no_asm_use}
 means that the assumptions are simplified but are not
  used in the simplification of each other or the conclusion.
\end{description}
Neither @{text"(no_asm_simp)"} nor @{text"(no_asm_use)"} allow to simplify
the above problematic subgoal.

Note that only one of the above options is allowed, and it must precede all
other arguments.
*}

subsubsection{*Rewriting with definitions*}

text{*\index{simplification!with definitions}
Constant definitions (\S\ref{sec:ConstDefinitions}) can
be used as simplification rules, but by default they are not.  Hence the
simplifier does not expand them automatically, just as it should be:
definitions are introduced for the purpose of abbreviating complex
concepts. Of course we need to expand the definitions initially to derive
enough lemmas that characterize the concept sufficiently for us to forget the
original definition. For example, given
*}

constdefs exor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
         "exor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)";

text{*\noindent
we may want to prove
*}

lemma "exor A (\<not>A)";

txt{*\noindent
Typically, the opening move consists in \emph{unfolding} the definition(s), which we need to
get started, but nothing else:\indexbold{*unfold}\indexbold{definition!unfolding}
*}

apply(simp only:exor_def);

txt{*\noindent
In this particular case, the resulting goal
@{subgoals[display,indent=0]}
can be proved by simplification. Thus we could have proved the lemma outright by
*}(*<*)oops;lemma "exor A (\<not>A)";(*>*)
apply(simp add: exor_def)
(*<*)done(*>*)
text{*\noindent
Of course we can also unfold definitions in the middle of a proof.

You should normally not turn a definition permanently into a simplification
rule because this defeats the whole purpose of an abbreviation.

\begin{warn}
  If you have defined $f\,x\,y~\isasymequiv~t$ then you can only expand
  occurrences of $f$ with at least two arguments. Thus it is safer to define
  $f$~\isasymequiv~\isasymlambda$x\,y.\;t$.
\end{warn}
*}

subsubsection{*Simplifying let-expressions*}

text{*\index{simplification!of let-expressions}
Proving a goal containing \isaindex{let}-expressions almost invariably
requires the @{text"let"}-con\-structs to be expanded at some point. Since
@{text"let"}-@{text"in"} is just syntactic sugar for a predefined constant
(called @{term"Let"}), expanding @{text"let"}-constructs means rewriting with
@{thm[source]Let_def}:
*}

lemma "(let xs = [] in xs@ys@xs) = ys";
apply(simp add: Let_def);
done

text{*
If, in a particular context, there is no danger of a combinatorial explosion
of nested @{text"let"}s one could even simlify with @{thm[source]Let_def} by
default:
*}
declare Let_def [simp]

subsubsection{*Conditional equations*}

text{*
So far all examples of rewrite rules were equations. The simplifier also
accepts \emph{conditional} equations, for example
*}

lemma hd_Cons_tl[simp]: "xs \<noteq> []  \<Longrightarrow>  hd xs # tl xs = xs";
apply(case_tac xs, simp, simp);
done

text{*\noindent
Note the use of ``\ttindexboldpos{,}{$Isar}'' to string together a
sequence of methods. Assuming that the simplification rule
@{term"(rev xs = []) = (xs = [])"}
is present as well,
*}

lemma "xs \<noteq> [] \<Longrightarrow> hd(rev xs) # tl(rev xs) = rev xs";
(*<*)
by(simp);
(*>*)
text{*\noindent
is proved by plain simplification:
the conditional equation @{thm[source]hd_Cons_tl} above
can simplify @{term"hd(rev xs) # tl(rev xs)"} to @{term"rev xs"}
because the corresponding precondition @{term"rev xs ~= []"}
simplifies to @{term"xs ~= []"}, which is exactly the local
assumption of the subgoal.
*}


subsubsection{*Automatic case splits*}

text{*\indexbold{case splits}\index{*split|(}
Goals containing @{text"if"}-expressions are usually proved by case
distinction on the condition of the @{text"if"}. For example the goal
*}

lemma "\<forall>xs. if xs = [] then rev xs = [] else rev xs \<noteq> []";

txt{*\noindent
can be split by a degenerate form of simplification
*}

apply(simp only: split: split_if);

txt{*\noindent
@{subgoals[display,indent=0]}
where no simplification rules are included (@{text"only:"} is followed by the
empty list of theorems) but the rule \isaindexbold{split_if} for
splitting @{text"if"}s is added (via the modifier @{text"split:"}). Because
case-splitting on @{text"if"}s is almost always the right proof strategy, the
simplifier performs it automatically. Try \isacommand{apply}@{text"(simp)"}
on the initial goal above.

This splitting idea generalizes from @{text"if"} to \isaindex{case}:
*}(*<*)oops;(*>*)

lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs";
apply(simp only: split: list.split);

txt{*
@{subgoals[display,indent=0]}
In contrast to @{text"if"}-expressions, the simplifier does not split
@{text"case"}-expressions by default because this can lead to nontermination
in case of recursive datatypes. Again, if the @{text"only:"} modifier is
dropped, the above goal is solved,
*}
(*<*)oops;
lemma "(case xs of [] \<Rightarrow> zs | y#ys \<Rightarrow> y#(ys@zs)) = xs@zs";
(*>*)
apply(simp split: list.split);
(*<*)done(*>*)
text{*\noindent%
which \isacommand{apply}@{text"(simp)"} alone will not do.

In general, every datatype $t$ comes with a theorem
$t$@{text".split"} which can be declared to be a \bfindex{split rule} either
locally as above, or by giving it the @{text"split"} attribute globally:
*}

declare list.split [split]

text{*\noindent
The @{text"split"} attribute can be removed with the @{text"del"} modifier,
either locally
*}
(*<*)
lemma "dummy=dummy";
(*>*)
apply(simp split del: split_if);
(*<*)
oops;
(*>*)
text{*\noindent
or globally:
*}
declare list.split [split del]

text{*
The above split rules intentionally only affect the conclusion of a
subgoal.  If you want to split an @{text"if"} or @{text"case"}-expression in
the assumptions, you have to apply @{thm[source]split_if_asm} or
$t$@{text".split_asm"}:
*}

lemma "if xs = [] then ys ~= [] else ys = [] ==> xs @ ys ~= []"
apply(simp only: split: split_if_asm);

txt{*\noindent
In contrast to splitting the conclusion, this actually creates two
separate subgoals (which are solved by @{text"simp_all"}):
@{subgoals[display,indent=0]}
If you need to split both in the assumptions and the conclusion,
use $t$@{text".splits"} which subsumes $t$@{text".split"} and
$t$@{text".split_asm"}. Analogously, there is @{thm[source]if_splits}.

\begin{warn}
  The simplifier merely simplifies the condition of an \isa{if} but not the
  \isa{then} or \isa{else} parts. The latter are simplified only after the
  condition reduces to \isa{True} or \isa{False}, or after splitting. The
  same is true for \isaindex{case}-expressions: only the selector is
  simplified at first, until either the expression reduces to one of the
  cases or it is split.
\end{warn}

\index{*split|)}
*}
(*<*)
by(simp_all)
(*>*)


subsubsection{*Arithmetic*}

text{*\index{arithmetic}
The simplifier routinely solves a small class of linear arithmetic formulae
(over type \isa{nat} and other numeric types): it only takes into account
assumptions and conclusions that are (possibly negated) (in)equalities
(@{text"="}, \isasymle, @{text"<"}) and it only knows about addition. Thus
*}

lemma "\<lbrakk> \<not> m < n; m < n+1 \<rbrakk> \<Longrightarrow> m = n"
(*<*)by(auto)(*>*)

text{*\noindent
is proved by simplification, whereas the only slightly more complex
*}

lemma "\<not> m < n \<and> m < n+1 \<Longrightarrow> m = n";
(*<*)by(arith)(*>*)

text{*\noindent
is not proved by simplification and requires @{text arith}.
*}


subsubsection{*Tracing*}
text{*\indexbold{tracing the simplifier}
Using the simplifier effectively may take a bit of experimentation.  Set the
\isaindexbold{trace_simp} \rmindex{flag} to get a better idea of what is going
on:
*}

ML "set trace_simp";
lemma "rev [a] = []";
apply(simp);
(*<*)oops(*>*)

text{*\noindent
produces the trace

\begin{ttbox}\makeatother
Applying instance of rewrite rule:
rev (?x1 \# ?xs1) == rev ?xs1 @ [?x1]
Rewriting:
rev [x] == rev [] @ [x]
Applying instance of rewrite rule:
rev [] == []
Rewriting:
rev [] == []
Applying instance of rewrite rule:
[] @ ?y == ?y
Rewriting:
[] @ [x] == [x]
Applying instance of rewrite rule:
?x3 \# ?t3 = ?t3 == False
Rewriting:
[x] = [] == False
\end{ttbox}

In more complicated cases, the trace can be quite lenghty, especially since
invocations of the simplifier are often nested (e.g.\ when solving conditions
of rewrite rules). Thus it is advisable to reset it:
*}

ML "reset trace_simp";

(*<*)
end
(*>*)
