(*<*)
theory Ifexpr imports Main begin;
(*>*)

subsection{*Case Study: Boolean Expressions*}

text{*\label{sec:boolex}\index{boolean expressions example|(}
The aim of this case study is twofold: it shows how to model boolean
expressions and some algorithms for manipulating them, and it demonstrates
the constructs introduced above.
*}

subsubsection{*Modelling Boolean Expressions*}

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

\subsubsection{The Value of a Boolean Expression}

The value of a boolean expression depends on the value of its variables.
Hence the function @{text"value"} takes an additional parameter, an
\emph{environment} of type @{typ"nat => bool"}, which maps variables to their
values:
*}

primrec "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"value (Const b) env = b" |
"value (Var x)   env = env x" |
"value (Neg b)   env = (\<not> value b env)" |
"value (And b c) env = (value b env \<and> value c env)"

text{*\noindent
\subsubsection{If-Expressions}

An alternative and often more efficient (because in a certain sense
canonical) representation are so-called \emph{If-expressions} built up
from constants (@{term"CIF"}), variables (@{term"VIF"}) and conditionals
(@{term"IF"}):
*}

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex;

text{*\noindent
The evaluation of If-expressions proceeds as for @{typ"boolex"}:
*}

primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"valif (CIF b)    env = b" |
"valif (VIF x)    env = env x" |
"valif (IF b t e) env = (if valif b env then valif t env
                                        else valif e env)"

text{*
\subsubsection{Converting Boolean and If-Expressions}

The type @{typ"boolex"} is close to the customary representation of logical
formulae, whereas @{typ"ifex"} is designed for efficiency. It is easy to
translate from @{typ"boolex"} into @{typ"ifex"}:
*}

primrec bool2if :: "boolex \<Rightarrow> ifex" where
"bool2if (Const b) = CIF b" |
"bool2if (Var x)   = VIF x" |
"bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)" |
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

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

primrec normif :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex" where
"normif (CIF b)    t e = IF (CIF b) t e" |
"normif (VIF x)    t e = IF (VIF x) t e" |
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"

primrec norm :: "ifex \<Rightarrow> ifex" where
"norm (CIF b)    = CIF b" |
"norm (VIF x)    = VIF x" |
"norm (IF b t e) = normif b (norm t) (norm e)"

text{*\noindent
Their interplay is tricky; we leave it to you to develop an
intuitive understanding. Fortunately, Isabelle can help us to verify that the
transformation preserves the value of the expression:
*}

theorem "valif (norm b) env = valif b env";(*<*)oops;(*>*)

text{*\noindent
The proof is canonical, provided we first show the following simplification
lemma, which also helps to understand what @{term"normif"} does:
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
the above sense? We define a function that tests If-expressions for normality:
*}

primrec normal :: "ifex \<Rightarrow> bool" where
"normal(CIF b) = True" |
"normal(VIF x) = True" |
"normal(IF b t e) = (normal t \<and> normal e \<and>
     (case b of CIF b \<Rightarrow> True | VIF x \<Rightarrow> True | IF x y z \<Rightarrow> False))"

text{*\noindent
Now we prove @{term"normal(norm b)"}. Of course, this requires a lemma about
normality of @{term"normif"}:
*}

lemma [simp]: "\<forall>t e. normal(normif b t e) = (normal t \<and> normal e)";
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
  We strengthen the definition of a @{const normal} If-expression as follows:
  the first argument of all @{term IF}s must be a variable. Adapt the above
  development to this changed requirement. (Hint: you may need to formulate
  some of the goals as implications (@{text"\<longrightarrow>"}) rather than
  equalities (@{text"="}).)
\end{exercise}
\index{boolean expressions example|)}
*}
(*<*)

primrec normif2 :: "ifex => ifex => ifex => ifex" where
"normif2 (CIF b)    t e = (if b then t else e)" |
"normif2 (VIF x)    t e = IF (VIF x) t e" |
"normif2 (IF b t e) u f = normif2 b (normif2 t u f) (normif2 e u f)"

primrec norm2 :: "ifex => ifex" where
"norm2 (CIF b)    = CIF b" |
"norm2 (VIF x)    = VIF x" |
"norm2 (IF b t e) = normif2 b (norm2 t) (norm2 e)"

primrec normal2 :: "ifex => bool" where
"normal2(CIF b) = True" |
"normal2(VIF x) = True" |
"normal2(IF b t e) = (normal2 t & normal2 e &
     (case b of CIF b => False | VIF x => True | IF x y z => False))"

lemma [simp]:
  "ALL t e. valif (normif2 b t e) env = valif (IF b t e) env"
apply(induct b)
by(auto)

theorem "valif (norm2 b) env = valif b env"
apply(induct b)
by(auto)

lemma [simp]: "ALL t e. normal2 t & normal2 e --> normal2(normif2 b t e)"
apply(induct b)
by(auto)

theorem "normal2(norm2 b)"
apply(induct b)
by(auto)

end
(*>*)
