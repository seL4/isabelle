(*<*)
theory ABexpr = Main:;
(*>*)

text{*
Sometimes it is necessary to define two datatypes that depend on each
other. This is called \textbf{mutual recursion}. As an example consider a
language of arithmetic and boolean expressions where
\begin{itemize}
\item arithmetic expressions contain boolean expressions because there are
  conditional arithmetic expressions like ``if $m<n$ then $n-m$ else $m-n$'',
  and
\item boolean expressions contain arithmetic expressions because of
  comparisons like ``$m<n$''.
\end{itemize}
In Isabelle this becomes
*}

datatype 'a aexp = IF   "'a bexp" "'a aexp" "'a aexp"
                 | Sum  "'a aexp" "'a aexp"
                 | Diff "'a aexp" "'a aexp"
                 | Var 'a
                 | Num nat
and      'a bexp = Less "'a aexp" "'a aexp"
                 | And  "'a bexp" "'a bexp"
                 | Neg  "'a bexp";

text{*\noindent
Type \isa{aexp} is similar to \isa{expr} in \S\ref{sec:ExprCompiler},
except that we have fixed the values to be of type \isa{nat} and that we
have fixed the two binary operations \isa{Sum} and \isa{Diff}. Boolean
expressions can be arithmetic comparisons, conjunctions and negations.
The semantics is fixed via two evaluation functions
*}

consts  evala :: "'a aexp \\<Rightarrow> ('a \\<Rightarrow> nat) \\<Rightarrow> nat"
        evalb :: "'a bexp \\<Rightarrow> ('a \\<Rightarrow> nat) \\<Rightarrow> bool";

text{*\noindent
that take an expression and an environment (a mapping from variables \isa{'a} to values
\isa{nat}) and return its arithmetic/boolean
value. Since the datatypes are mutually recursive, so are functions that
operate on them. Hence they need to be defined in a single \isacommand{primrec}
section:
*}

primrec
  "evala (IF b a1 a2) env =
     (if evalb b env then evala a1 env else evala a2 env)"
  "evala (Sum a1 a2) env = evala a1 env + evala a2 env"
  "evala (Diff a1 a2) env = evala a1 env - evala a2 env"
  "evala (Var v) env = env v"
  "evala (Num n) env = n"

  "evalb (Less a1 a2) env = (evala a1 env < evala a2 env)"
  "evalb (And b1 b2) env = (evalb b1 env \\<and> evalb b2 env)"
  "evalb (Neg b) env = (\\<not> evalb b env)"

text{*\noindent
In the same fashion we also define two functions that perform substitution:
*}

consts substa :: "('a \\<Rightarrow> 'b aexp) \\<Rightarrow> 'a aexp \\<Rightarrow> 'b aexp"
       substb :: "('a \\<Rightarrow> 'b aexp) \\<Rightarrow> 'a bexp \\<Rightarrow> 'b bexp";

text{*\noindent
The first argument is a function mapping variables to expressions, the
substitution. It is applied to all variables in the second argument. As a
result, the type of variables in the expression may change from \isa{'a}
to \isa{'b}. Note that there are only arithmetic and no boolean variables.
*}

primrec
  "substa s (IF b a1 a2) =
     IF (substb s b) (substa s a1) (substa s a2)"
  "substa s (Sum a1 a2) = Sum (substa s a1) (substa s a2)"
  "substa s (Diff a1 a2) = Diff (substa s a1) (substa s a2)"
  "substa s (Var v) = s v"
  "substa s (Num n) = Num n"

  "substb s (Less a1 a2) = Less (substa s a1) (substa s a2)"
  "substb s (And b1 b2) = And (substb s b1) (substb s b2)"
  "substb s (Neg b) = Neg (substb s b)";

text{*
Now we can prove a fundamental theorem about the interaction between
evaluation and substitution: applying a substitution $s$ to an expression $a$
and evaluating the result in an environment $env$ yields the same result as
evaluation $a$ in the environment that maps every variable $x$ to the value
of $s(x)$ under $env$. If you try to prove this separately for arithmetic or
boolean expressions (by induction), you find that you always need the other
theorem in the induction step. Therefore you need to state and prove both
theorems simultaneously:
*}

lemma "evala (substa s a) env = evala a (\\<lambda>x. evala (s x) env) \\<and>
        evalb (substb s b) env = evalb b (\\<lambda>x. evala (s x) env)";
apply(induct_tac a and b);

txt{*\noindent
The resulting 8 goals (one for each constructor) are proved in one fell swoop:
*}

apply auto.;

text{*
In general, given $n$ mutually recursive datatypes $\tau@1$, \dots, $\tau@n$,
an inductive proof expects a goal of the form
\[ P@1(x@1)\ \land \dots \land P@n(x@n) \]
where each variable $x@i$ is of type $\tau@i$. Induction is started by
\begin{ttbox}
apply(induct_tac \(x@1\) \texttt{and} \(\dots\) \texttt{and} \(x@n\));
\end{ttbox}

\begin{exercise}
  Define a function \isa{norma} of type \isa{'a aexp \isasymFun\ 'a aexp} that
  replaces \isa{IF}s with complex boolean conditions by nested
  \isa{IF}s where each condition is a \isa{Less} --- \isa{And} and
  \isa{Neg} should be eliminated completely. Prove that \isa{norma}
  preserves the value of an expression and that the result of \isa{norma}
  is really normal, i.e.\ no more \isa{And}s and \isa{Neg}s occur in
  it.  ({\em Hint:} proceed as in \S\ref{sec:boolex}).
\end{exercise}
*}
(*<*)
end
(*>*)
