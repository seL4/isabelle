theory ToyList = PreList:

text{*\noindent
HOL already has a predefined theory of lists called @{text"List"} ---
@{text"ToyList"} is merely a small fragment of it chosen as an example. In
contrast to what is recommended in \S\ref{sec:Basic:Theories},
@{text"ToyList"} is not based on @{text"Main"} but on @{text"PreList"}, a
theory that contains pretty much everything but lists, thus avoiding
ambiguities caused by defining lists twice.
*}

datatype 'a list = Nil                          ("[]")
                 | Cons 'a "'a list"            (infixr "#" 65);

text{*\noindent
\index{datatype@\isacommand {datatype} (command)}
The datatype \tydx{list} introduces two
constructors \cdx{Nil} and \cdx{Cons}, the
empty~list and the operator that adds an element to the front of a list. For
example, the term \isa{Cons True (Cons False Nil)} is a value of
type @{typ"bool list"}, namely the list with the elements @{term"True"} and
@{term"False"}. Because this notation quickly becomes unwieldy, the
datatype declaration is annotated with an alternative syntax: instead of
@{term[source]Nil} and \isa{Cons x xs} we can write
@{term"[]"}\index{$HOL2list@\texttt{[]}|bold} and
@{term"x # xs"}\index{$HOL2list@\texttt{\#}|bold}. In fact, this
alternative syntax is the familiar one.  Thus the list \isa{Cons True
(Cons False Nil)} becomes @{term"True # False # []"}. The annotation
\isacommand{infixr}\index{infixr@\isacommand{infixr} (annotation)} 
means that @{text"#"} associates to
the right: the term @{term"x # y # z"} is read as @{text"x # (y # z)"}
and not as @{text"(x # y) # z"}.
The @{text 65} is the priority of the infix @{text"#"}.

\begin{warn}
  Syntax annotations are can be powerful, but they are difficult to master and 
  are never necessary.  You
  could drop them from theory @{text"ToyList"} and go back to the identifiers
  @{term[source]Nil} and @{term[source]Cons}.
  Novices should avoid using
  syntax annotations in their own theories.
\end{warn}
Next, two functions @{text"app"} and \cdx{rev} are declared:
*}

consts app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"   (infixr "@" 65)
       rev :: "'a list \<Rightarrow> 'a list";

text{*
\noindent
In contrast to many functional programming languages,
Isabelle insists on explicit declarations of all functions
(keyword \commdx{consts}).  Apart from the declaration-before-use
restriction, the order of items in a theory file is unconstrained. Function
@{text"app"} is annotated with concrete syntax too. Instead of the
prefix syntax @{text"app xs ys"} the infix
@{term"xs @ ys"}\index{$HOL2list@\texttt{\at}|bold} becomes the preferred
form. Both functions are defined recursively:
*}

primrec
"[] @ ys       = ys"
"(x # xs) @ ys = x # (xs @ ys)";

primrec
"rev []        = []"
"rev (x # xs)  = (rev xs) @ (x # [])";

text{*
\noindent\index{*rev (constant)|(}\index{append function|(}
The equations for @{text"app"} and @{term"rev"} hardly need comments:
@{text"app"} appends two lists and @{term"rev"} reverses a list.  The
keyword \commdx{primrec} indicates that the recursion is
of a particularly primitive kind where each recursive call peels off a datatype
constructor from one of the arguments.  Thus the
recursion always terminates, i.e.\ the function is \textbf{total}.
\index{functions!total}

The termination requirement is absolutely essential in HOL, a logic of total
functions. If we were to drop it, inconsistencies would quickly arise: the
``definition'' $f(n) = f(n)+1$ immediately leads to $0 = 1$ by subtracting
$f(n)$ on both sides.
% However, this is a subtle issue that we cannot discuss here further.

\begin{warn}
  As we have indicated, the requirement for total functions is an essential characteristic of HOL\@. It is only
  because of totality that reasoning in HOL is comparatively easy.  More
  generally, the philosophy in HOL is to refrain from asserting arbitrary axioms (such as
  function definitions whose totality has not been proved) because they
  quickly lead to inconsistencies. Instead, fixed constructs for introducing
  types and functions are offered (such as \isacommand{datatype} and
  \isacommand{primrec}) which are guaranteed to preserve consistency.
\end{warn}

\index{syntax}%
A remark about syntax.  The textual definition of a theory follows a fixed
syntax with keywords like \isacommand{datatype} and \isacommand{end}.
% (see Fig.~\ref{fig:keywords} in Appendix~\ref{sec:Appendix} for a full list).
Embedded in this syntax are the types and formulae of HOL, whose syntax is
extensible (see \S\ref{sec:syntax-anno}), e.g.\ by new user-defined infix operators.
To distinguish the two levels, everything
HOL-specific (terms and types) should be enclosed in
\texttt{"}\dots\texttt{"}. 
To lessen this burden, quotation marks around a single identifier can be
dropped, unless the identifier happens to be a keyword, as in
*}

consts "end" :: "'a list \<Rightarrow> 'a"

text{*\noindent
When Isabelle prints a syntax error message, it refers to the HOL syntax as
the \textbf{inner syntax} and the enclosing theory language as the \textbf{outer syntax}.


\section{An Introductory Proof}
\label{sec:intro-proof}

Assuming you have input the declarations and definitions of \texttt{ToyList}
presented so far, we are ready to prove a few simple theorems. This will
illustrate not just the basic proof commands but also the typical proof
process.

\subsubsection*{Main Goal.}

Our goal is to show that reversing a list twice produces the original
list.
*}

theorem rev_rev [simp]: "rev(rev xs) = xs";

txt{*\index{theorem@\isacommand {theorem} (command)|bold}%
\noindent
This \isacommand{theorem} command does several things:
\begin{itemize}
\item
It establishes a new theorem to be proved, namely @{prop"rev(rev xs) = xs"}.
\item
It gives that theorem the name @{text"rev_rev"}, for later reference.
\item
It tells Isabelle (via the bracketed attribute \attrdx{simp}) to take the eventual theorem as a simplification rule: future proofs involving
simplification will replace occurrences of @{term"rev(rev xs)"} by
@{term"xs"}.
\end{itemize}
The name and the simplification attribute are optional.
Isabelle's response is to print
\begin{isabelle}
proof(prove):~step~0\isanewline
\isanewline
goal~(theorem~rev\_rev):\isanewline
rev~(rev~xs)~=~xs\isanewline
~1.~rev~(rev~xs)~=~xs
\end{isabelle}
The first three lines tell us that we are 0 steps into the proof of
theorem @{text"rev_rev"}; for compactness reasons we rarely show these
initial lines in this tutorial. The remaining lines display the current
\rmindex{proof state}.
Until we have finished a proof, the proof state always looks like this:
\begin{isabelle}
$G$\isanewline
~1.~$G\sb{1}$\isanewline
~~\vdots~~\isanewline
~$n$.~$G\sb{n}$
\end{isabelle}
where $G$
is the overall goal that we are trying to prove, and the numbered lines
contain the subgoals $G\sb{1}$, \dots, $G\sb{n}$ that we need to prove to
establish $G$.\index{subgoals}
At @{text"step 0"} there is only one subgoal, which is
identical with the overall goal.  Normally $G$ is constant and only serves as
a reminder. Hence we rarely show it in this tutorial.

Let us now get back to @{prop"rev(rev xs) = xs"}. Properties of recursively
defined functions are best established by induction. In this case there is
nothing obvious except induction on @{term"xs"}:
*}

apply(induct_tac xs);

txt{*\noindent\index{*induct_tac (method)}%
This tells Isabelle to perform induction on variable @{term"xs"}. The suffix
@{term"tac"} stands for \textbf{tactic},\index{tactics}
a synonym for ``theorem proving function''.
By default, induction acts on the first subgoal. The new proof state contains
two subgoals, namely the base case (@{term[source]Nil}) and the induction step
(@{term[source]Cons}):
@{subgoals[display,indent=0,margin=65]}

The induction step is an example of the general format of a subgoal:\index{subgoals}
\begin{isabelle}
~$i$.~{\isasymAnd}$x\sb{1}$~\dots~$x\sb{n}$.~{\it assumptions}~{\isasymLongrightarrow}~{\it conclusion}
\end{isabelle}\index{$IsaAnd@\isasymAnd|bold}
The prefix of bound variables \isasymAnd$x\sb{1}$~\dots~$x\sb{n}$ can be
ignored most of the time, or simply treated as a list of variables local to
this subgoal. Their deeper significance is explained in Chapter~\ref{chap:rules}.
The {\it assumptions}\index{assumptions!of subgoal}
are the local assumptions for this subgoal and {\it
  conclusion}\index{conclusion!of subgoal} is the actual proposition to be proved. 
Typical proof steps
that add new assumptions are induction and case distinction. In our example
the only assumption is the induction hypothesis @{term"rev (rev list) =
  list"}, where @{term"list"} is a variable name chosen by Isabelle. If there
are multiple assumptions, they are enclosed in the bracket pair
\indexboldpos{\isasymlbrakk}{$Isabrl} and
\indexboldpos{\isasymrbrakk}{$Isabrr} and separated by semicolons.

Let us try to solve both goals automatically:
*}

apply(auto);

txt{*\noindent
This command tells Isabelle to apply a proof strategy called
@{text"auto"} to all subgoals. Essentially, @{text"auto"} tries to
simplify the subgoals.  In our case, subgoal~1 is solved completely (thanks
to the equation @{prop"rev [] = []"}) and disappears; the simplified version
of subgoal~2 becomes the new subgoal~1:
@{subgoals[display,indent=0,margin=70]}
In order to simplify this subgoal further, a lemma suggests itself.
*}
(*<*)
oops
(*>*)

subsubsection{*First Lemma*}

text{*
\indexbold{abandoning a proof}\indexbold{proofs!abandoning}
After abandoning the above proof attempt (at the shell level type
\commdx{oops}) we start a new proof:
*}

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)";

txt{*\noindent The keywords \commdx{theorem} and
\commdx{lemma} are interchangeable and merely indicate
the importance we attach to a proposition.  Therefore we use the words
\emph{theorem} and \emph{lemma} pretty much interchangeably, too.

There are two variables that we could induct on: @{term"xs"} and
@{term"ys"}. Because @{text"@"} is defined by recursion on
the first argument, @{term"xs"} is the correct one:
*}

apply(induct_tac xs);

txt{*\noindent
This time not even the base case is solved automatically:
*}

apply(auto);

txt{*
@{subgoals[display,indent=0,goals_limit=1]}
Again, we need to abandon this proof attempt and prove another simple lemma
first. In the future the step of abandoning an incomplete proof before
embarking on the proof of a lemma usually remains implicit.
*}
(*<*)
oops
(*>*)

subsubsection{*Second Lemma*}

text{*
We again try the canonical proof procedure:
*}

lemma app_Nil2 [simp]: "xs @ [] = xs";
apply(induct_tac xs);
apply(auto);

txt{*
\noindent
It works, yielding the desired message @{text"No subgoals!"}:
@{goals[display,indent=0]}
We still need to confirm that the proof is now finished:
*}

done

text{*\noindent
As a result of that final \commdx{done}, Isabelle associates the lemma just proved
with its name. In this tutorial, we sometimes omit to show that final \isacommand{done}
if it is obvious from the context that the proof is finished.

% Instead of \isacommand{apply} followed by a dot, you can simply write
% \isacommand{by}\indexbold{by}, which we do most of the time.
Notice that in lemma @{thm[source]app_Nil2},
as printed out after the final \isacommand{done}, the free variable @{term"xs"} has been
replaced by the unknown @{text"?xs"}, just as explained in
\S\ref{sec:variables}.

Going back to the proof of the first lemma
*}

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)";
apply(induct_tac xs);
apply(auto);

txt{*
\noindent
we find that this time @{text"auto"} solves the base case, but the
induction step merely simplifies to
@{subgoals[display,indent=0,goals_limit=1]}
Now we need to remember that @{text"@"} associates to the right, and that
@{text"#"} and @{text"@"} have the same priority (namely the @{text"65"}
in their \isacommand{infixr} annotation). Thus the conclusion really is
\begin{isabelle}
~~~~~(rev~ys~@~rev~list)~@~(a~\#~[])~=~rev~ys~@~(rev~list~@~(a~\#~[]))
\end{isabelle}
and the missing lemma is associativity of @{text"@"}.
*}
(*<*)oops(*>*)

subsubsection{*Third Lemma*}

text{*
Abandoning the previous attempt, the canonical proof procedure
succeeds without further ado.
*}

lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)";
apply(induct_tac xs);
apply(auto);
done

text{*
\noindent
Now we can prove the first lemma:
*}

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)";
apply(induct_tac xs);
apply(auto);
done

text{*\noindent
Finally, we prove our main theorem:
*}

theorem rev_rev [simp]: "rev(rev xs) = xs";
apply(induct_tac xs);
apply(auto);
done

text{*\noindent
The final \commdx{end} tells Isabelle to close the current theory because
we are finished with its development:%
\index{*rev (constant)|)}\index{append function|)}
*}

end
