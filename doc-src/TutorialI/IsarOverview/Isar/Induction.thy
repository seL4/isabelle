(*<*)theory Induction = Main:(*>*)

section{*Case distinction and induction \label{sec:Induct}*}

text{* Computer science applications abound with inductively defined
structures, which is why we treat them in more detail. HOL already
comes with a datatype of lists with the two constructors @{text Nil}
and @{text Cons}. @{text Nil} is written @{term"[]"} and @{text"Cons x
xs"} is written @{term"x # xs"}.  *}

subsection{*Case distinction*}

text{* We have already met the @{text cases} method for performing
binary case splits. Here is another example: *}
lemma "\<not> A \<or> A"
proof cases
  assume "A" thus ?thesis ..
next
  assume "\<not> A" thus ?thesis ..
qed

text{*\noindent The two cases must come in this order because @{text
cases} merely abbreviates @{text"(rule case_split_thm)"} where
@{thm[source] case_split_thm} is @{thm case_split_thm}. If we reverse
the order of the two cases in the proof, the first case would prove
@{prop"\<not> A \<Longrightarrow> \<not> A \<or> A"} which would solve the first premise of
@{thm[source] case_split_thm}, instantiating @{text ?P} with @{term "\<not>
A"}, thus making the second premise @{prop"\<not> \<not> A \<Longrightarrow> \<not> A \<or> A"}.
Therefore the order of subgoals is not always completely arbitrary.

The above proof is appropriate if @{term A} is textually small.
However, if @{term A} is large, we do not want to repeat it. This can
be avoided by the following idiom *}

lemma "\<not> A \<or> A"
proof (cases "A")
  case True thus ?thesis ..
next
  case False thus ?thesis ..
qed

text{*\noindent which is like the previous proof but instantiates
@{text ?P} right away with @{term A}. Thus we could prove the two
cases in any order. The phrase `\isakeyword{case}~@{text True}'
abbreviates `\isakeyword{assume}~@{text"True: A"}' and analogously for
@{text"False"} and @{prop"\<not>A"}.

The same game can be played with other datatypes, for example lists,
where @{term tl} is the tail of a list, and @{text length} returns a
natural number:
\Tweakskip
*}
(*<*)declare length_tl[simp del](*>*)
lemma "length(tl xs) = length xs - 1"
proof (cases xs)
  case Nil thus ?thesis by simp
next
  case Cons thus ?thesis by simp
qed
text{*\noindent Here `\isakeyword{case}~@{text Nil}' abbreviates
`\isakeyword{assume}~@{text"Nil:"}~@{prop"xs = []"}' and
`\isakeyword{case}~@{text Cons}'
abbreviates `\isakeyword{fix}~@{text"? ??"}
\isakeyword{assume}~@{text"Cons:"}~@{text"xs = ? # ??"}'
where @{text"?"} and @{text"??"}
stand for variable names that have been chosen by the system.
Therefore we cannot refer to them.
Luckily, this proof is simple enough we do not need to refer to them.
However, sometimes one may have to. Hence Isar offers a simple scheme for
naming those variables: replace the anonymous @{text Cons} by
@{text"(Cons y ys)"}, which abbreviates `\isakeyword{fix}~@{text"y ys"}
\isakeyword{assume}~@{text"Cons:"}~@{text"xs = y # ys"}'.
In each \isakeyword{case} the assumption can be
referred to inside the proof by the name of the constructor. In
Section~\ref{sec:full-Ind} below we will come across an example
of this. *}

subsection{*Structural induction*}

text{* We start with an inductive proof where both cases are proved automatically: *}
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
by (induct n, simp_all)

text{*\noindent If we want to expose more of the structure of the
proof, we can use pattern matching to avoid having to repeat the goal
statement: *}
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)" (is "?P n")
proof (induct n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P(Suc n)" by simp
qed

text{* \noindent We could refine this further to show more of the equational
proof. Instead we explore the same avenue as for case distinctions:
introducing context via the \isakeyword{case} command: *}
lemma "2 * (\<Sum>i<n+1. i) = n*(n+1)"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc thus ?case by simp
qed

text{* \noindent The implicitly defined @{text ?case} refers to the
corresponding case to be proved, i.e.\ @{text"?P 0"} in the first case and
@{text"?P(Suc n)"} in the second case. Context \isakeyword{case}~@{text 0} is
empty whereas \isakeyword{case}~@{text Suc} assumes @{text"?P n"}. Again we
have the same problem as with case distinctions: we cannot refer to an anonymous @{term n}
in the induction step because it has not been introduced via \isakeyword{fix}
(in contrast to the previous proof). The solution is the one outlined for
@{text Cons} above: replace @{term Suc} by @{text"(Suc i)"}: *}
lemma fixes n::nat shows "n < n*n + 1"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc i) thus "Suc i < Suc i * Suc i + 1" by simp
qed

text{* \noindent Of course we could again have written
\isakeyword{thus}~@{text ?case} instead of giving the term explicitly
but we wanted to use @{term i} somewhere. *}

subsection{*Induction formulae involving @{text"\<And>"} or @{text"\<Longrightarrow>"}\label{sec:full-Ind}*}

text{* Let us now consider the situation where the goal to be proved contains
@{text"\<And>"} or @{text"\<Longrightarrow>"}, say @{prop"\<And>x. P x \<Longrightarrow> Q x"} --- motivation and a
real example follow shortly.  This means that in each case of the induction,
@{text ?case} would be of the form @{prop"\<And>x. P' x \<Longrightarrow> Q' x"}.  Thus the
first proof steps will be the canonical ones, fixing @{text x} and assuming
@{prop"P' x"}. To avoid this tedium, induction performs these steps
automatically: for example in case @{text"(Suc n)"}, @{text ?case} is only
@{prop"Q' x"} whereas the assumptions (named @{term Suc}!) contain both the
usual induction hypothesis \emph{and} @{prop"P' x"}.
It should be clear how this generalises to more complex formulae.

As an example we will now prove complete induction via
structural induction. *}

lemma assumes A: "(\<And>n. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  shows "P(n::nat)"
proof (rule A)
  show "\<And>m. m < n \<Longrightarrow> P m"
  proof (induct n)
    case 0 thus ?case by simp
  next
    case (Suc n)   -- {*\isakeyword{fix} @{term m} \isakeyword{assume} @{text Suc}: @{text[source]"?m < n \<Longrightarrow> P ?m"} @{prop[source]"m < Suc n"}*}
    show ?case    -- {*@{term ?case}*}
    proof cases
      assume eq: "m = n"
      from Suc and A have "P n" by blast
      with eq show "P m" by simp
    next
      assume "m \<noteq> n"
      with Suc have "m < n" by arith
      thus "P m" by(rule Suc)
    qed
  qed
qed
text{* \noindent Given the explanations above and the comments in the
proof text (only necessary for novices), the proof should be quite
readable.

The statement of the lemma is interesting because it deviates from the style in
the Tutorial~\cite{LNCS2283}, which suggests to introduce @{text"\<forall>"} or
@{text"\<longrightarrow>"} into a theorem to strengthen it for induction. In Isar
proofs we can use @{text"\<And>"} and @{text"\<Longrightarrow>"} instead. This simplifies the
proof and means we do not have to convert between the two kinds of
connectives.

Note that in a nested induction over the same data type, the inner
case labels hide the outer ones of the same name. If you want to refer
to the outer ones inside, you need to name them on the outside, e.g.\
\isakeyword{note}~@{text"outer_IH = Suc"}.  *}

subsection{*Rule induction*}

text{* HOL also supports inductively defined sets. See \cite{LNCS2283}
for details. As an example we define our own version of the reflexive
transitive closure of a relation --- HOL provides a predefined one as well.*}
consts rtc :: "('a \<times> 'a)set \<Rightarrow> ('a \<times> 'a)set"   ("_*" [1000] 999)
inductive "r*"
intros
refl:  "(x,x) \<in> r*"
step:  "\<lbrakk> (x,y) \<in> r; (y,z) \<in> r* \<rbrakk> \<Longrightarrow> (x,z) \<in> r*"

text{* \noindent
First the constant is declared as a function on binary
relations (with concrete syntax @{term"r*"} instead of @{text"rtc
r"}), then the defining clauses are given. We will now prove that
@{term"r*"} is indeed transitive: *}

lemma assumes A: "(x,y) \<in> r*" shows "(y,z) \<in> r* \<Longrightarrow> (x,z) \<in> r*"
using A
proof induct
  case refl thus ?case .
next
  case step thus ?case by(blast intro: rtc.step)
qed
text{*\noindent Rule induction is triggered by a fact $(x_1,\dots,x_n)
\in R$ piped into the proof, here \isakeyword{using}~@{text A}. The
proof itself follows the inductive definition very
closely: there is one case for each rule, and it has the same name as
the rule, analogous to structural induction.

However, this proof is rather terse. Here is a more readable version:
*}

lemma assumes A: "(x,y) \<in> r*" and B: "(y,z) \<in> r*"
  shows "(x,z) \<in> r*"
proof -
  from A B show ?thesis
  proof induct
    fix x assume "(x,z) \<in> r*"  -- {*@{text B}[@{text y} := @{text x}]*}
    thus "(x,z) \<in> r*" .
  next
    fix x' x y
    assume 1: "(x',x) \<in> r" and
           IH: "(y,z) \<in> r* \<Longrightarrow> (x,z) \<in> r*" and
           B:  "(y,z) \<in> r*"
    from 1 IH[OF B] show "(x',z) \<in> r*" by(rule rtc.step)
  qed
qed
text{*\noindent We start the proof with \isakeyword{from}~@{text"A
B"}. Only @{text A} is ``consumed'' by the induction step.
Since @{text B} is left over we don't just prove @{text
?thesis} but @{text"B \<Longrightarrow> ?thesis"}, just as in the previous proof. The
base case is trivial. In the assumptions for the induction step we can
see very clearly how things fit together and permit ourselves the
obvious forward step @{text"IH[OF B]"}.

The notation `\isakeyword{case}~\isa{(}\emph{constructor} \emph{vars}\isa{)}'
is also supported for inductive definitions. The \emph{constructor} is (the
name of) the rule and the \emph{vars} fix the free variables in the
rule; the order of the \emph{vars} must correspond to the
\emph{alphabetical order} of the variables as they appear in the rule.
For example, we could start the above detailed proof of the induction
with \isakeyword{case}~\isa{(step x' x y)}. However, we can then only
refer to the assumptions named \isa{step} collectively and not
individually, as the above proof requires.  *}

subsection{*More induction*}

text{* We close the section by demonstrating how arbitrary induction
rules are applied. As a simple example we have chosen recursion
induction, i.e.\ induction based on a recursive function
definition. However, most of what we show works for induction in
general.

The example is an unusual definition of rotation: *}

consts rot :: "'a list \<Rightarrow> 'a list"
recdef rot "measure length"  --"for the internal termination proof"
"rot [] = []"
"rot [x] = [x]"
"rot (x#y#zs) = y # rot(x#zs)"
text{*\noindent This yields, among other things, the induction rule
@{thm[source]rot.induct}: @{thm[display]rot.induct[no_vars]}
In the following proof we rely on a default naming scheme for cases: they are
called 1, 2, etc, unless they have been named explicitly. The latter happens
only with datatypes and inductively defined sets, but not with recursive
functions. *}

lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"
proof (induct xs rule: rot.induct)
  case 1 thus ?case by simp
next
  case 2 show ?case by simp
next
  case (3 a b cs)
  have "rot (a # b # cs) = b # rot(a # cs)" by simp
  also have "\<dots> = b # tl(a # cs) @ [hd(a # cs)]" by(simp add:3)
  also have "\<dots> = tl (a # b # cs) @ [hd (a # b # cs)]" by simp
  finally show ?case .
qed

text{*\noindent
The third case is only shown in gory detail (see \cite{BauerW-TPHOLs01}
for how to reason with chains of equations) to demonstrate that the
`\isakeyword{case}~\isa{(}\emph{constructor} \emph{vars}\isa{)}' notation also
works for arbitrary induction theorems with numbered cases. The order
of the \emph{vars} corresponds to the order of the
@{text"\<And>"}-quantified variables in each case of the induction
theorem. For induction theorems produced by \isakeyword{recdef} it is
the order in which the variables appear on the left-hand side of the
equation.

The proof is so simple that it can be condensed to
\Tweakskip*}
(*<*)lemma "xs \<noteq> [] \<Longrightarrow> rot xs = tl xs @ [hd xs]"(*>*)
by (induct xs rule: rot.induct, simp_all)

(*<*)end(*>*)
