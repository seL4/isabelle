theory ToyList
imports Main
begin

text\<open>\noindent
HOL already has a predefined theory of lists called \<open>List\<close> ---
\<open>ToyList\<close> is merely a small fragment of it chosen as an example.
To avoid some ambiguities caused by defining lists twice, we manipulate
the concrete syntax and name space of theory \<^theory>\<open>Main\<close> as follows.
\<close>

no_notation Nil  ("[]") and Cons  (infixr "#" 65) and append  (infixr "@" 65)
hide_type list
hide_const rev

datatype 'a list = Nil                          ("[]")
                 | Cons 'a "'a list"            (infixr "#" 65)

text\<open>\noindent
The datatype\index{datatype@\isacommand {datatype} (command)}
\tydx{list} introduces two
constructors \cdx{Nil} and \cdx{Cons}, the
empty~list and the operator that adds an element to the front of a list. For
example, the term \isa{Cons True (Cons False Nil)} is a value of
type \<^typ>\<open>bool list\<close>, namely the list with the elements \<^term>\<open>True\<close> and
\<^term>\<open>False\<close>. Because this notation quickly becomes unwieldy, the
datatype declaration is annotated with an alternative syntax: instead of
@{term[source]Nil} and \isa{Cons x xs} we can write
\<^term>\<open>[]\<close>\index{$HOL2list@\isa{[]}|bold} and
\<^term>\<open>x # xs\<close>\index{$HOL2list@\isa{\#}|bold}. In fact, this
alternative syntax is the familiar one.  Thus the list \isa{Cons True
(Cons False Nil)} becomes \<^term>\<open>True # False # []\<close>. The annotation
\isacommand{infixr}\index{infixr@\isacommand{infixr} (annotation)} 
means that \<open>#\<close> associates to
the right: the term \<^term>\<open>x # y # z\<close> is read as \<open>x # (y # z)\<close>
and not as \<open>(x # y) # z\<close>.
The \<open>65\<close> is the priority of the infix \<open>#\<close>.

\begin{warn}
  Syntax annotations can be powerful, but they are difficult to master and 
  are never necessary.  You
  could drop them from theory \<open>ToyList\<close> and go back to the identifiers
  @{term[source]Nil} and @{term[source]Cons}.  Novices should avoid using
  syntax annotations in their own theories.
\end{warn}
Next, two functions \<open>app\<close> and \cdx{rev} are defined recursively,
in this order, because Isabelle insists on definition before use:
\<close>

primrec app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65) where
"[] @ ys       = ys" |
"(x # xs) @ ys = x # (xs @ ys)"

primrec rev :: "'a list \<Rightarrow> 'a list" where
"rev []        = []" |
"rev (x # xs)  = (rev xs) @ (x # [])"

text\<open>\noindent
Each function definition is of the form
\begin{center}
\isacommand{primrec} \textit{name} \<open>::\<close> \textit{type} \textit{(optional syntax)} \isakeyword{where} \textit{equations}
\end{center}
The equations must be separated by \<open>|\<close>.
%
Function \<open>app\<close> is annotated with concrete syntax. Instead of the
prefix syntax \<open>app xs ys\<close> the infix
\<^term>\<open>xs @ ys\<close>\index{$HOL2list@\isa{\at}|bold} becomes the preferred
form.

\index{*rev (constant)|(}\index{append function|(}
The equations for \<open>app\<close> and \<^term>\<open>rev\<close> hardly need comments:
\<open>app\<close> appends two lists and \<^term>\<open>rev\<close> reverses a list.  The
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
extensible (see \S\ref{sec:concrete-syntax}), e.g.\ by new user-defined infix operators.
To distinguish the two levels, everything
HOL-specific (terms and types) should be enclosed in
\texttt{"}\dots\texttt{"}. 
To lessen this burden, quotation marks around a single identifier can be
dropped, unless the identifier happens to be a keyword, for example
\isa{"end"}.
When Isabelle prints a syntax error message, it refers to the HOL syntax as
the \textbf{inner syntax} and the enclosing theory language as the \textbf{outer syntax}.

Comments\index{comment} must be in enclosed in \texttt{(*}and\texttt{*)}.

\section{Evaluation}
\index{evaluation}

Assuming you have processed the declarations and definitions of
\texttt{ToyList} presented so far, you may want to test your
functions by running them. For example, what is the value of
\<^term>\<open>rev(True#False#[])\<close>? Command
\<close>

value "rev (True # False # [])"

text\<open>\noindent yields the correct result \<^term>\<open>False # True # []\<close>.
But we can go beyond mere functional programming and evaluate terms with
variables in them, executing functions symbolically:\<close>

value "rev (a # b # c # [])"

text\<open>\noindent yields \<^term>\<open>c # b # a # []\<close>.

\section{An Introductory Proof}
\label{sec:intro-proof}

Having convinced ourselves (as well as one can by testing) that our
definitions capture our intentions, we are ready to prove a few simple
theorems. This will illustrate not just the basic proof commands but
also the typical proof process.

\subsubsection*{Main Goal.}

Our goal is to show that reversing a list twice produces the original
list.
\<close>

theorem rev_rev [simp]: "rev(rev xs) = xs"

txt\<open>\index{theorem@\isacommand {theorem} (command)|bold}%
\noindent
This \isacommand{theorem} command does several things:
\begin{itemize}
\item
It establishes a new theorem to be proved, namely \<^prop>\<open>rev(rev xs) = xs\<close>.
\item
It gives that theorem the name \<open>rev_rev\<close>, for later reference.
\item
It tells Isabelle (via the bracketed attribute \attrdx{simp}) to take the eventual theorem as a simplification rule: future proofs involving
simplification will replace occurrences of \<^term>\<open>rev(rev xs)\<close> by
\<^term>\<open>xs\<close>.
\end{itemize}
The name and the simplification attribute are optional.
Isabelle's response is to print the initial proof state consisting
of some header information (like how many subgoals there are) followed by
@{subgoals[display,indent=0]}
For compactness reasons we omit the header in this tutorial.
Until we have finished a proof, the \rmindex{proof state} proper
always looks like this:
\begin{isabelle}
~1.~$G\sb{1}$\isanewline
~~\vdots~~\isanewline
~$n$.~$G\sb{n}$
\end{isabelle}
The numbered lines contain the subgoals $G\sb{1}$, \dots, $G\sb{n}$
that we need to prove to establish the main goal.\index{subgoals}
Initially there is only one subgoal, which is identical with the
main goal. (If you always want to see the main goal as well,
set the flag \isa{Proof.show_main_goal}\index{*show_main_goal (flag)}
--- this flag used to be set by default.)

Let us now get back to \<^prop>\<open>rev(rev xs) = xs\<close>. Properties of recursively
defined functions are best established by induction. In this case there is
nothing obvious except induction on \<^term>\<open>xs\<close>:
\<close>

apply(induct_tac xs)

txt\<open>\noindent\index{*induct_tac (method)}%
This tells Isabelle to perform induction on variable \<^term>\<open>xs\<close>. The suffix
\<^term>\<open>tac\<close> stands for \textbf{tactic},\index{tactics}
a synonym for ``theorem proving function''.
By default, induction acts on the first subgoal. The new proof state contains
two subgoals, namely the base case (@{term[source]Nil}) and the induction step
(@{term[source]Cons}):
@{subgoals[display,indent=0,margin=65]}

The induction step is an example of the general format of a subgoal:\index{subgoals}
\begin{isabelle}
~$i$.~{\isasymAnd}$x\sb{1}$~\dots$x\sb{n}$.~{\it assumptions}~{\isasymLongrightarrow}~{\it conclusion}
\end{isabelle}\index{$IsaAnd@\isasymAnd|bold}
The prefix of bound variables \isasymAnd$x\sb{1}$~\dots~$x\sb{n}$ can be
ignored most of the time, or simply treated as a list of variables local to
this subgoal. Their deeper significance is explained in Chapter~\ref{chap:rules}.
The {\it assumptions}\index{assumptions!of subgoal}
are the local assumptions for this subgoal and {\it
  conclusion}\index{conclusion!of subgoal} is the actual proposition to be proved. 
Typical proof steps
that add new assumptions are induction and case distinction. In our example
the only assumption is the induction hypothesis \<^term>\<open>rev (rev list) =
  list\<close>, where \<^term>\<open>list\<close> is a variable name chosen by Isabelle. If there
are multiple assumptions, they are enclosed in the bracket pair
\indexboldpos{\isasymlbrakk}{$Isabrl} and
\indexboldpos{\isasymrbrakk}{$Isabrr} and separated by semicolons.

Let us try to solve both goals automatically:
\<close>

apply(auto)

txt\<open>\noindent
This command tells Isabelle to apply a proof strategy called
\<open>auto\<close> to all subgoals. Essentially, \<open>auto\<close> tries to
simplify the subgoals.  In our case, subgoal~1 is solved completely (thanks
to the equation \<^prop>\<open>rev [] = []\<close>) and disappears; the simplified version
of subgoal~2 becomes the new subgoal~1:
@{subgoals[display,indent=0,margin=70]}
In order to simplify this subgoal further, a lemma suggests itself.
\<close>
(*<*)
oops
(*>*)

subsubsection\<open>First Lemma\<close>

text\<open>
\indexbold{abandoning a proof}\indexbold{proofs!abandoning}
After abandoning the above proof attempt (at the shell level type
\commdx{oops}) we start a new proof:
\<close>

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)"

txt\<open>\noindent The keywords \commdx{theorem} and
\commdx{lemma} are interchangeable and merely indicate
the importance we attach to a proposition.  Therefore we use the words
\emph{theorem} and \emph{lemma} pretty much interchangeably, too.

There are two variables that we could induct on: \<^term>\<open>xs\<close> and
\<^term>\<open>ys\<close>. Because \<open>@\<close> is defined by recursion on
the first argument, \<^term>\<open>xs\<close> is the correct one:
\<close>

apply(induct_tac xs)

txt\<open>\noindent
This time not even the base case is solved automatically:
\<close>

apply(auto)

txt\<open>
@{subgoals[display,indent=0,goals_limit=1]}
Again, we need to abandon this proof attempt and prove another simple lemma
first. In the future the step of abandoning an incomplete proof before
embarking on the proof of a lemma usually remains implicit.
\<close>
(*<*)
oops
(*>*)

subsubsection\<open>Second Lemma\<close>

text\<open>
We again try the canonical proof procedure:
\<close>

lemma app_Nil2 [simp]: "xs @ [] = xs"
apply(induct_tac xs)
apply(auto)

txt\<open>
\noindent
It works, yielding the desired message \<open>No subgoals!\<close>:
@{goals[display,indent=0]}
We still need to confirm that the proof is now finished:
\<close>

done

text\<open>\noindent
As a result of that final \commdx{done}, Isabelle associates the lemma just proved
with its name. In this tutorial, we sometimes omit to show that final \isacommand{done}
if it is obvious from the context that the proof is finished.

% Instead of \isacommand{apply} followed by a dot, you can simply write
% \isacommand{by}\indexbold{by}, which we do most of the time.
Notice that in lemma @{thm[source]app_Nil2},
as printed out after the final \isacommand{done}, the free variable \<^term>\<open>xs\<close> has been
replaced by the unknown \<open>?xs\<close>, just as explained in
\S\ref{sec:variables}.

Going back to the proof of the first lemma
\<close>

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)"
apply(induct_tac xs)
apply(auto)

txt\<open>
\noindent
we find that this time \<open>auto\<close> solves the base case, but the
induction step merely simplifies to
@{subgoals[display,indent=0,goals_limit=1]}
Now we need to remember that \<open>@\<close> associates to the right, and that
\<open>#\<close> and \<open>@\<close> have the same priority (namely the \<open>65\<close>
in their \isacommand{infixr} annotation). Thus the conclusion really is
\begin{isabelle}
~~~~~(rev~ys~@~rev~list)~@~(a~\#~[])~=~rev~ys~@~(rev~list~@~(a~\#~[]))
\end{isabelle}
and the missing lemma is associativity of \<open>@\<close>.
\<close>
(*<*)oops(*>*)

subsubsection\<open>Third Lemma\<close>

text\<open>
Abandoning the previous attempt, the canonical proof procedure
succeeds without further ado.
\<close>

lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
apply(induct_tac xs)
apply(auto)
done

text\<open>
\noindent
Now we can prove the first lemma:
\<close>

lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)"
apply(induct_tac xs)
apply(auto)
done

text\<open>\noindent
Finally, we prove our main theorem:
\<close>

theorem rev_rev [simp]: "rev(rev xs) = xs"
apply(induct_tac xs)
apply(auto)
done

text\<open>\noindent
The final \commdx{end} tells Isabelle to close the current theory because
we are finished with its development:%
\index{*rev (constant)|)}\index{append function|)}
\<close>

end
