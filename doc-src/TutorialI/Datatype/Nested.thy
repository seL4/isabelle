(*<*)
theory Nested = Main:;
(*>*)

text{*
So far, all datatypes had the property that on the right-hand side of their
definition they occurred only at the top-level, i.e.\ directly below a
constructor. This is not the case any longer for the following model of terms
where function symbols can be applied to a list of arguments:
*}

datatype ('a,'b)"term" = Var 'a | App 'b "('a,'b)term list";

text{*\noindent
Note that we need to quote \isa{term} on the left to avoid confusion with
the command \isacommand{term}.
Parameter \isa{'a} is the type of variables and \isa{'b} the type of
function symbols.
A mathematical term like $f(x,g(y))$ becomes \isa{App f [Var x, App g
  [Var y]]}, where \isa{f}, \isa{g}, \isa{x}, \isa{y} are
suitable values, e.g.\ numbers or strings.

What complicates the definition of \isa{term} is the nested occurrence of
\isa{term} inside \isa{list} on the right-hand side. In principle,
nested recursion can be eliminated in favour of mutual recursion by unfolding
the offending datatypes, here \isa{list}. The result for \isa{term}
would be something like
\medskip

\input{Datatype/document/unfoldnested.tex}
\medskip

\noindent
Although we do not recommend this unfolding to the user, it shows how to
simulate nested recursion by mutual recursion.
Now we return to the initial definition of \isa{term} using
nested recursion.

Let us define a substitution function on terms. Because terms involve term
lists, we need to define two substitution functions simultaneously:
*}

consts
subst :: "('a\\<Rightarrow>('a,'b)term) \\<Rightarrow> ('a,'b)term      \\<Rightarrow> ('a,'b)term"
substs:: "('a\\<Rightarrow>('a,'b)term) \\<Rightarrow> ('a,'b)term list \\<Rightarrow> ('a,'b)term list";

primrec
  "subst s (Var x) = s x"
  "subst s (App f ts) = App f (substs s ts)"

  "substs s [] = []"
  "substs s (t # ts) = subst s t # substs s ts";

text{*\noindent
Similarly, when proving a statement about terms inductively, we need
to prove a related statement about term lists simultaneously. For example,
the fact that the identity substitution does not change a term needs to be
strengthened and proved as follows:
*}

lemma "subst  Var t  = (t ::('a,'b)term)  \\<and>
        substs Var ts = (ts::('a,'b)term list)";
by(induct_tac t and ts, auto);

text{*\noindent
Note that \isa{Var} is the identity substitution because by definition it
leaves variables unchanged: \isa{subst Var (Var $x$) = Var $x$}. Note also
that the type annotations are necessary because otherwise there is nothing in
the goal to enforce that both halves of the goal talk about the same type
parameters \isa{('a,'b)}. As a result, induction would fail
because the two halves of the goal would be unrelated.

\begin{exercise}
The fact that substitution distributes over composition can be expressed
roughly as follows:
\begin{ttbox}
subst (f o g) t = subst f (subst g t)
\end{ttbox}
Correct this statement (you will find that it does not type-check),
strengthen it, and prove it. (Note: \ttindexbold{o} is function composition;
its definition is found in theorem \isa{o_def}).
\end{exercise}

Of course, you may also combine mutual and nested recursion. For example,
constructor \isa{Sum} in \S\ref{sec:datatype-mut-rec} could take a list of
expressions as its argument: \isa{Sum "'a aexp list"}.
*}
(*<*)

lemma "subst s (App f ts) = App f (map (subst s) ts)";
by(induct_tac ts, auto);

end
(*>*)
