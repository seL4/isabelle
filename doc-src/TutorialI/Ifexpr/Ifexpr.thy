(*<*)
theory Ifexpr = Main:;
(*>*)

text{*
\subsubsection{How can we model boolean expressions?}

We want to represent boolean expressions built up from variables and
constants by negation and conjunction. The following datatype serves exactly
that purpose:
*}

datatype boolex = Const bool | Var nat | Neg boolex
                | And boolex boolex;

text{*\noindent
The two constants are represented by \isa{Const~True} and
\isa{Const~False}. Variables are represented by terms of the form
\isa{Var~$n$}, where $n$ is a natural number (type \isa{nat}).
For example, the formula $P@0 \land \neg P@1$ is represented by the term
\isa{And~(Var~0)~(Neg(Var~1))}.

\subsubsection{What is the value of a boolean expression?}

The value of a boolean expression depends on the value of its variables.
Hence the function \isa{value} takes an additional parameter, an {\em
  environment} of type \isa{nat \isasymFun\ bool}, which maps variables to
their values:
*}

consts value :: "boolex \\<Rightarrow> (nat \\<Rightarrow> bool) \\<Rightarrow> bool";
primrec
"value (Const b) env = b"
"value (Var x)   env = env x"
"value (Neg b)   env = (\\<not> value b env)"
"value (And b c) env = (value b env \\<and> value c env)";

text{*\noindent
\subsubsection{If-expressions}

An alternative and often more efficient (because in a certain sense
canonical) representation are so-called \emph{If-expressions} built up
from constants (\isa{CIF}), variables (\isa{VIF}) and conditionals
(\isa{IF}):
*}

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex;

text{*\noindent
The evaluation if If-expressions proceeds as for \isa{boolex}:
*}

consts valif :: "ifex \\<Rightarrow> (nat \\<Rightarrow> bool) \\<Rightarrow> bool";
primrec
"valif (CIF b)    env = b"
"valif (VIF x)    env = env x"
"valif (IF b t e) env = (if valif b env then valif t env
                                        else valif e env)";

text{*
\subsubsection{Transformation into and of If-expressions}

The type \isa{boolex} is close to the customary representation of logical
formulae, whereas \isa{ifex} is designed for efficiency. It is easy to
translate from \isa{boolex} into \isa{ifex}:
*}

consts bool2if :: "boolex \\<Rightarrow> ifex";
primrec
"bool2if (Const b) = CIF b"
"bool2if (Var x)   = VIF x"
"bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)"
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)";

text{*\noindent
At last, we have something we can verify: that \isa{bool2if} preserves the
value of its argument:
*}

lemma "valif (bool2if b) env = value b env";

txt{*\noindent
The proof is canonical:
*}

apply(induct_tac b);
by(auto);

text{*\noindent
In fact, all proofs in this case study look exactly like this. Hence we do
not show them below.

More interesting is the transformation of If-expressions into a normal form
where the first argument of \isa{IF} cannot be another \isa{IF} but
must be a constant or variable. Such a normal form can be computed by
repeatedly replacing a subterm of the form \isa{IF~(IF~b~x~y)~z~u} by
\isa{IF b (IF x z u) (IF y z u)}, which has the same value. The following
primitive recursive functions perform this task:
*}

consts normif :: "ifex \\<Rightarrow> ifex \\<Rightarrow> ifex \\<Rightarrow> ifex";
primrec
"normif (CIF b)    t e = IF (CIF b) t e"
"normif (VIF x)    t e = IF (VIF x) t e"
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)";

consts norm :: "ifex \\<Rightarrow> ifex";
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
lemma (which also helps to understand what \isa{normif} does):
*}

lemma [simp]:
  "\\<forall>t e. valif (normif b t e) env = valif (IF b t e) env";
(*<*)
apply(induct_tac b);
by(auto);

theorem "valif (norm b) env = valif b env";
apply(induct_tac b);
by(auto);
(*>*)
text{*\noindent
Note that the lemma does not have a name, but is implicitly used in the proof
of the theorem shown above because of the \isa{[simp]} attribute.

But how can we be sure that \isa{norm} really produces a normal form in
the above sense? We define a function that tests If-expressions for normality
*}

consts normal :: "ifex \\<Rightarrow> bool";
primrec
"normal(CIF b) = True"
"normal(VIF x) = True"
"normal(IF b t e) = (normal t \\<and> normal e \\<and>
     (case b of CIF b \\<Rightarrow> True | VIF x \\<Rightarrow> True | IF x y z \\<Rightarrow> False))";

text{*\noindent
and prove \isa{normal(norm b)}. Of course, this requires a lemma about
normality of \isa{normif}:
*}

lemma[simp]: "\\<forall>t e. normal(normif b t e) = (normal t \\<and> normal e)";
(*<*)
apply(induct_tac b);
by(auto);

theorem "normal(norm b)";
apply(induct_tac b);
by(auto);

end
(*>*)
