(*<*)
theory termination = examples:
(*>*)

text{*
When a function~$f$ is defined via \isacommand{recdef}, Isabelle tries to prove
its termination with the help of the user-supplied measure.  Each of the examples
above is simple enough that Isabelle can automatically prove that the
argument's measure decreases in each recursive call. As a result,
$f$@{text".simps"} will contain the defining equations (or variants derived
from them) as theorems. For example, look (via \isacommand{thm}) at
@{thm[source]sep.simps} and @{thm[source]sep1.simps} to see that they define
the same function. What is more, those equations are automatically declared as
simplification rules.

Isabelle may fail to prove the termination condition for some
recursive call.  Let us try to define Quicksort:*}

consts qs :: "nat list \<Rightarrow> nat list"
recdef(*<*)(permissive)(*>*) qs "measure length"
 "qs [] = []"
 "qs(x#xs) = qs(filter (\<lambda>y. y\<le>x) xs) @ [x] @ qs(filter (\<lambda>y. x<y) xs)"

text{*\noindent where @{term filter} is predefined and @{term"filter P xs"}
is the list of elements of @{term xs} satisfying @{term P}.
This definition of @{term qs} fails, and Isabelle prints an error message
showing you what it was unable to prove:
@{text[display]"length (filter ... xs) < Suc (length xs)"}
We can either prove this as a separate lemma, or try to figure out which
existing lemmas may help. We opt for the second alternative. The theory of
lists contains the simplification rule @{thm length_filter[no_vars]},
which is already
close to what we need, except that we still need to turn \mbox{@{text"< Suc"}}
into
@{text"\<le>"} for the simplification rule to apply. Lemma
@{thm[source]less_Suc_eq_le} does just that: @{thm less_Suc_eq_le[no_vars]}.

Now we retry the above definition but supply the lemma(s) just found (or
proved). Because \isacommand{recdef}'s termination prover involves
simplification, we include in our second attempt a hint: the
\attrdx{recdef_simp} attribute says to use @{thm[source]less_Suc_eq_le} as a
simplification rule.  *}

(*<*)global consts qs :: "nat list \<Rightarrow> nat list" (*>*)
recdef qs "measure length"
 "qs [] = []"
 "qs(x#xs) = qs(filter (\<lambda>y. y\<le>x) xs) @ [x] @ qs(filter (\<lambda>y. x<y) xs)"
(hints recdef_simp: less_Suc_eq_le)
(*<*)local(*>*)
text{*\noindent
This time everything works fine. Now @{thm[source]qs.simps} contains precisely
the stated recursion equations for @{text qs} and they have become
simplification rules.
Thus we can automatically prove results such as this one:
*}

theorem "qs[2,3,0] = qs[3,0,2]"
apply(simp)
done

text{*\noindent
More exciting theorems require induction, which is discussed below.

If the termination proof requires a lemma that is of general use, you can
turn it permanently into a simplification rule, in which case the above
\isacommand{hint} is not necessary. But in the case of
@{thm[source]less_Suc_eq_le} this would be of dubious value.
*}
(*<*)
end
(*>*)
