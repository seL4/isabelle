(*<*)
theory termination = Main:;
(*>*)

text{*
When a function is defined via \isacommand{recdef}, Isabelle tries to prove
its termination with the help of the user-supplied measure.  All of the above
examples are simple enough that Isabelle can prove automatically that the
measure of the argument goes down in each recursive call. As a result,
\isa{$f$.simps} will contain the defining equations (or variants derived from
them) as theorems. For example, look (via \isacommand{thm}) at
\isa{sep.simps} and \isa{sep1.simps} to see that they define the same
function. What is more, those equations are automatically declared as
simplification rules.

In general, Isabelle may not be able to prove all termination condition
(there is one for each recursive call) automatically. For example,
termination of the following artificial function
*}

consts f :: "nat*nat \\<Rightarrow> nat";
recdef f "measure(\\<lambda>(x,y). x-y)"
  "f(x,y) = (if x \\<le> y then x else f(x,y+1))";

text{*\noindent
is not proved automatically (although maybe it should be). Isabelle prints a
kind of error message showing you what it was unable to prove. You will then
have to prove it as a separate lemma before you attempt the definition
of your function once more. In our case the required lemma is the obvious one:
*}

lemma termi_lem[simp]: "\\<not> x \\<le> y \\<Longrightarrow> x - Suc y < x - y";

txt{*\noindent
It was not proved automatically because of the special nature of \isa{-}
on \isa{nat}. This requires more arithmetic than is tried by default:
*}

apply(arith).;

text{*\noindent
Because \isacommand{recdef}'s termination prover involves simplification,
we have turned our lemma into a simplification rule. Therefore our second
attempt to define our function will automatically take it into account:
*}

consts g :: "nat*nat \\<Rightarrow> nat";
recdef g "measure(\\<lambda>(x,y). x-y)"
  "g(x,y) = (if x \\<le> y then x else g(x,y+1))";

text{*\noindent
This time everything works fine. Now \isa{g.simps} contains precisely the
stated recursion equation for \isa{g} and they are simplification
rules. Thus we can automatically prove
*}

theorem wow: "g(1,0) = g(1,1)";
apply(simp).;

text{*\noindent
More exciting theorems require induction, which is discussed below.

Because lemma \isa{termi_lem} above was only turned into a
simplification rule for the sake of the termination proof, we may want to
disable it again:
*}

lemmas [simp del] = termi_lem;

text{*
The attentive reader may wonder why we chose to call our function \isa{g}
rather than \isa{f} the second time around. The reason is that, despite
the failed termination proof, the definition of \isa{f} did not
fail (and thus we could not define it a second time). However, all theorems
about \isa{f}, for example \isa{f.simps}, carry as a precondition the
unproved termination condition. Moreover, the theorems \isa{f.simps} are
not simplification rules. However, this mechanism allows a delayed proof of
termination: instead of proving \isa{termi_lem} up front, we could prove
it later on and then use it to remove the preconditions from the theorems
about \isa{f}. In most cases this is more cumbersome than proving things
up front
%FIXME, with one exception: nested recursion.

Although all the above examples employ measure functions, \isacommand{recdef}
allows arbitrary wellfounded relations. For example, termination of
Ackermann's function requires the lexicographic product \isa{<*lex*>}:
*}

consts ack :: "nat*nat \\<Rightarrow> nat";
recdef ack "measure(%m. m) <*lex*> measure(%n. n)"
  "ack(0,n)         = Suc n"
  "ack(Suc m,0)     = ack(m, 1)"
  "ack(Suc m,Suc n) = ack(m,ack(Suc m,n))";

text{*\noindent
For details see the manual~\cite{isabelle-HOL} and the examples in the
library.
*}

(*<*)
end
(*>*)
