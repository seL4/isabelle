(*<*)
theory Ifexpr = Main:;
(*>*)

subsection{*Case Study: Boolean Expressions*}

text{*\label{sec:boolex}
The aim of this case study is twofold: it shows how to model boolean
expressions and some algorithms for manipulating them, and it demonstrates
the constructs introduced above.
*}

subsubsection{*How Can We Model Boolean Expressions?*}

text{*
We want to represent boolean expressions built up from variables and
constants by negation and conjunction. The following datatype serves exactly
that purpose:
*}

datatype boolex = Const bool | Var nat | Neg boolex
                | And boolex boolex;

text{*\noindent
The two constants are represented by @{term"Const True"} and
@{term"Const False"}. Variables are represented by terms of the form
@{term"Var n"}, where @{term"n"} is a natural number (type @{typ"nat"}).
For example, the formula $P@0 \land \neg P@1$ is represented by the term
@{term"And (Var 0) (Neg(Var 1))"}.

\subsubsection{What is the Value of a Boolean Expression?}

The value of a boolean expression depends on the value of its variables.
Hence the function @{text"value"} takes an additional parameter, an
\emph{environment} of type @{typ"nat => bool"}, which maps variables to their
values:
*}

consts value :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool";
primrec
"value (Const b) env = b"
"value (Var x)   env = env x"
"value (Neg b)   env = (\<not> value b env)"
"value (And b c) env = (value b env \<and> value c env)";

text{*\noindent
\subsubsection{If-Expressions}

An alternative and often more efficient (because in a certain sense
canonical) representation are so-called \emph{If-expressions} built up
from constants (@{term"CIF"}), variables (@{term"VIF"}) and conditionals
(@{term"IF"}):
*}

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex;

text{*\noindent
The evaluation if If-expressions proceeds as for @{typ"boolex"}:
*}

consts valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool";
primrec
"valif (CIF b)    env = b"
"valif (VIF x)    env = env x"
"valif (IF b t e) env = (if valif b env then valif t env
                                        else valif e env)";

text{*
\subsubsection{Transformation Into and of If-Expressions}

\REMARK{is this the title you wanted?}
The type @{typ"boolex"} is close to the customary representation of logical
formulae, whereas @{typ"ifex"} is designed for efficiency. It is easy to
translate from @{typ"boolex"} into @{typ"ifex"}:
*}

consts bool2if :: "boolex \<Rightarrow> ifex";
primrec
"bool2if (Const b) = CIF b"
"bool2if (Var x)   = VIF x"
"bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)"
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)";

text{*\noindent
At last, we have something we can verify: that @{term"bool2if"} preserves the
value of its argument:
*}

lemma "valif (bool2if b) env = value b env";

txt{*\noindent
The proof is canonical:
*}

apply(induct_tac b);
apply(auto);
done

text{*\noindent
In fact, all proofs in this case study look exactly like this. Hence we do
not show them below.

More interesting is the transformation of If-expressions into a normal form
where the first argument of @{term"IF"} cannot be another @{term"IF"} but
must be a constant or variable. Such a normal form can be computed by
repeatedly replacing a subterm of the form @{term"IF (IF b x y) z u"} by
@{term"IF b (IF x z u) (IF y z u)"}, which has the same value. The following
primitive recursive functions perform this task:
*}

consts normif :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex";
primrec
"normif (CIF b)    t e = IF (CIF b) t e"
"normif (VIF x)    t e = IF (VIF x) t e"
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)";

consts norm :: "ifex \<Rightarrow> ifex";
primrec
"norm (CIF b)    = CIF b"
"norm (VIF x)    = VIF x"
"norm (IF b t e) = normif b (norm t) (norm e)";

text{*\noindent
Their interplay is a bit tricky, and we leave it to the reader to develop an
intuitive understanding. Fortunately, Isabelle can help us to verify that the
transformation preserves the value of the expression:
*}

theorem "valif (norm b) env = valif b env";(*<*)oops;(*>*)

text{*\noindent
The proof is canonical, provided we first show the following simplification
lemma (which also helps to understand what @{term"normif"} does):
*}

lemma [simp]:
  "\<forall>t e. valif (normif b t e) env = valif (IF b t e) env";
(*<*)
apply(induct_tac b);
by(auto);

theorem "valif (norm b) env = valif b env";
apply(induct_tac b);
by(auto);
(*>*)
text{*\noindent
Note that the lemma does not have a name, but is implicitly used in the proof
of the theorem shown above because of the @{text"[simp]"} attribute.

But how can we be sure that @{term"norm"} really produces a normal form in
the above sense? We define a function that tests If-expressions for normality
*}

consts normal :: "ifex \<Rightarrow> bool";
primrec
"normal(CIF b) = True"
"normal(VIF x) = True"
"normal(IF b t e) = (normal t \<and> normal e \<and>
     (case b of CIF b \<Rightarrow> True | VIF x \<Rightarrow> True | IF x y z \<Rightarrow> False))";

text{*\noindent
and prove @{term"normal(norm b)"}. Of course, this requires a lemma about
normality of @{term"normif"}:
*}

lemma[simp]: "\<forall>t e. normal(normif b t e) = (normal t \<and> normal e)";
(*<*)
apply(induct_tac b);
by(auto);

theorem "normal(norm b)";
apply(induct_tac b);
by(auto);
(*>*)

text{*\medskip
How do we come up with the required lemmas? Try to prove the main theorems
without them and study carefully what @{text auto} leaves unproved. This 
can provide the clue.  The necessity of universal quantification
(@{text"\<forall>t e"}) in the two lemmas is explained in
\S\ref{sec:InductionHeuristics}

\begin{exercise}
  We strengthen the definition of a @{term normal} If-expression as follows:
  the first argument of all @{term IF}s must be a variable. Adapt the above
  development to this changed requirement. (Hint: you may need to formulate
  some of the goals as implications (@{text"\<longrightarrow>"}) rather than
  equalities (@{text"="}).)
\end{exercise}
*}
(*<*)
end
(*>*)
