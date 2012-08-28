(*<*)
theory Nested imports ABexpr begin
(*>*)

text{*
\index{datatypes!and nested recursion}%
So far, all datatypes had the property that on the right-hand side of their
definition they occurred only at the top-level: directly below a
constructor. Now we consider \emph{nested recursion}, where the recursive
datatype occurs nested in some other datatype (but not inside itself!).
Consider the following model of terms
where function symbols can be applied to a list of arguments:
*}
(*<*)hide_const Var(*>*)
datatype ('v,'f)"term" = Var 'v | App 'f "('v,'f)term list";

text{*\noindent
Note that we need to quote @{text term} on the left to avoid confusion with
the Isabelle command \isacommand{term}.
Parameter @{typ"'v"} is the type of variables and @{typ"'f"} the type of
function symbols.
A mathematical term like $f(x,g(y))$ becomes @{term"App f [Var x, App g
  [Var y]]"}, where @{term f}, @{term g}, @{term x}, @{term y} are
suitable values, e.g.\ numbers or strings.

What complicates the definition of @{text term} is the nested occurrence of
@{text term} inside @{text list} on the right-hand side. In principle,
nested recursion can be eliminated in favour of mutual recursion by unfolding
the offending datatypes, here @{text list}. The result for @{text term}
would be something like
\medskip

\input{unfoldnested.tex}
\medskip

\noindent
Although we do not recommend this unfolding to the user, it shows how to
simulate nested recursion by mutual recursion.
Now we return to the initial definition of @{text term} using
nested recursion.

Let us define a substitution function on terms. Because terms involve term
lists, we need to define two substitution functions simultaneously:
*}

primrec
subst :: "('v\<Rightarrow>('v,'f)term) \<Rightarrow> ('v,'f)term      \<Rightarrow> ('v,'f)term" and
substs:: "('v\<Rightarrow>('v,'f)term) \<Rightarrow> ('v,'f)term list \<Rightarrow> ('v,'f)term list"
where
"subst s (Var x) = s x" |
  subst_App:
"subst s (App f ts) = App f (substs s ts)" |

"substs s [] = []" |
"substs s (t # ts) = subst s t # substs s ts"

text{*\noindent
Individual equations in a \commdx{primrec} definition may be
named as shown for @{thm[source]subst_App}.
The significance of this device will become apparent below.

Similarly, when proving a statement about terms inductively, we need
to prove a related statement about term lists simultaneously. For example,
the fact that the identity substitution does not change a term needs to be
strengthened and proved as follows:
*}

lemma subst_id(*<*)(*referred to from ABexpr*)(*>*): "subst  Var t  = (t ::('v,'f)term)  \<and>
                  substs Var ts = (ts::('v,'f)term list)";
apply(induct_tac t and ts, simp_all);
done

text{*\noindent
Note that @{term Var} is the identity substitution because by definition it
leaves variables unchanged: @{prop"subst Var (Var x) = Var x"}. Note also
that the type annotations are necessary because otherwise there is nothing in
the goal to enforce that both halves of the goal talk about the same type
parameters @{text"('v,'f)"}. As a result, induction would fail
because the two halves of the goal would be unrelated.

\begin{exercise}
The fact that substitution distributes over composition can be expressed
roughly as follows:
@{text[display]"subst (f \<circ> g) t = subst f (subst g t)"}
Correct this statement (you will find that it does not type-check),
strengthen it, and prove it. (Note: @{text"\<circ>"} is function composition;
its definition is found in theorem @{thm[source]o_def}).
\end{exercise}
\begin{exercise}\label{ex:trev-trev}
  Define a function @{term trev} of type @{typ"('v,'f)term => ('v,'f)term"}
that recursively reverses the order of arguments of all function symbols in a
  term. Prove that @{prop"trev(trev t) = t"}.
\end{exercise}

The experienced functional programmer may feel that our definition of
@{term subst} is too complicated in that @{const substs} is
unnecessary. The @{term App}-case can be defined directly as
@{term[display]"subst s (App f ts) = App f (map (subst s) ts)"}
where @{term"map"} is the standard list function such that
@{text"map f [x1,...,xn] = [f x1,...,f xn]"}. This is true, but Isabelle
insists on the conjunctive format. Fortunately, we can easily \emph{prove}
that the suggested equation holds:
*}
(*<*)
(* Exercise 1: *)
lemma "subst  ((subst f) \<circ> g) t  = subst  f (subst g t) \<and>
       substs ((subst f) \<circ> g) ts = substs f (substs g ts)"
apply (induct_tac t and ts)
apply (simp_all)
done

(* Exercise 2: *)

primrec trev :: "('v,'f) term \<Rightarrow> ('v,'f) term"
  and trevs:: "('v,'f) term list \<Rightarrow> ('v,'f) term list"
where
  "trev (Var v)    = Var v"
| "trev (App f ts) = App f (trevs ts)"
| "trevs [] = []"
| "trevs (t#ts) = (trevs ts) @ [(trev t)]" 

lemma [simp]: "\<forall> ys. trevs (xs @ ys) = (trevs ys) @ (trevs xs)" 
apply (induct_tac xs, auto)
done

lemma "trev (trev t) = (t::('v,'f)term) \<and> 
       trevs (trevs ts) = (ts::('v,'f)term list)"
apply (induct_tac t and ts, simp_all)
done
(*>*)

lemma [simp]: "subst s (App f ts) = App f (map (subst s) ts)"
apply(induct_tac ts, simp_all)
done

text{*\noindent
What is more, we can now disable the old defining equation as a
simplification rule:
*}

declare subst_App [simp del]

text{*\noindent The advantage is that now we have replaced @{const
substs} by @{const map}, we can profit from the large number of
pre-proved lemmas about @{const map}.  Unfortunately, inductive proofs
about type @{text term} are still awkward because they expect a
conjunction. One could derive a new induction principle as well (see
\S\ref{sec:derive-ind}), but simpler is to stop using
\isacommand{primrec} and to define functions with \isacommand{fun}
instead.  Simple uses of \isacommand{fun} are described in
\S\ref{sec:fun} below.  Advanced applications, including functions
over nested datatypes like @{text term}, are discussed in a
separate tutorial~\cite{isabelle-function}.

Of course, you may also combine mutual and nested recursion of datatypes. For example,
constructor @{text Sum} in \S\ref{sec:datatype-mut-rec} could take a list of
expressions as its argument: @{text Sum}~@{typ[quotes]"'a aexp list"}.
*}
(*<*)end(*>*)
