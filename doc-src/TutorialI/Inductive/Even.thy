(* ID:         $Id$ *)
theory Even = Main:

text{*We begin with a simple example: the set of even numbers.  Obviously this
concept can be expressed already using the divides relation (dvd).  We shall
prove below that the two formulations coincide.

First, we declare the constant \isa{even} to be a set of natural numbers.
Then, an inductive declaration gives it the desired properties.
*}


consts even :: "nat set"
inductive even
intros
zero[intro!]: "0 \<in> even"
step[intro!]: "n \<in> even \<Longrightarrow> (Suc (Suc n)) \<in> even"

text{*An inductive definition consists of introduction rules.  The first one
above states that 0 is even; the second states that if $n$ is even, so is
$n+2$.  Given this declaration, Isabelle generates a fixed point definition
for \isa{even} and proves many theorems about it.  These theorems include the
introduction rules specified in the declaration, an elimination rule for case
analysis and an induction rule.  We can refer to these theorems by
automatically-generated names:

@{thm[display] even.step[no_vars]}
\rulename{even.step}

@{thm[display] even.induct[no_vars]}
\rulename{even.induct}

Attributes can be given to the introduction rules.  Here both rules are
specified as \isa{intro!}, which will cause them to be applied aggressively.
Obviously, regarding 0 as even is always safe.  The second rule is also safe
because $n+2$ is even if and only if $n$ is even.  We prove this equivalence
later.*}

text{*Our first lemma states that numbers of the form $2\times k$ are even.
Introduction rules are used to show that given values belong to the inductive
set.  Often, as here, the proof involves some other sort of induction.*}
lemma two_times_even[intro!]: "#2*k \<in> even"
apply (induct "k")
 apply auto
done

text{* The first step is induction on the natural number \isa{k}, which leaves
two subgoals:

pr(latex xsymbols symbols);
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ two{\isacharunderscore}times{\isacharunderscore}even{\isacharparenright}{\isacharcolon}\isanewline
{\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ k\ {\isasymin}\ even\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ {\isadigit{0}}\ {\isasymin}\ even\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymAnd}n{\isachardot}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ n\ {\isasymin}\ even\ {\isasymLongrightarrow}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ Suc\ n\ {\isasymin}\ even

Here \isa{auto} simplifies both subgoals so that they match the introduction
rules, which then are applied automatically.  *}

text{*Our goal is to prove the equivalence between the traditional definition
of even (using the divides relation) and our inductive definition.  Half of
this equivalence is trivial using the lemma just proved, whose \isa{intro!}
attribute ensures it will be applied automatically.  *}

lemma dvd_imp_even: "#2 dvd n \<Longrightarrow> n \<in> even"
apply (auto simp add: dvd_def)
done

text{*our first rule induction!*}
lemma even_imp_dvd: "n \<in> even \<Longrightarrow> #2 dvd n"
apply (erule even.induct)
 apply simp
apply (simp add: dvd_def)
apply clarify
apply (rule_tac x = "Suc k" in exI)
apply simp
done
text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ even{\isacharunderscore}imp{\isacharunderscore}dvd{\isacharparenright}{\isacharcolon}\isanewline
n\ {\isasymin}\ even\ {\isasymLongrightarrow}\ {\isacharhash}{\isadigit{2}}\ dvd\ n\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isacharhash}{\isadigit{2}}\ dvd\ {\isadigit{0}}\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymAnd}n{\isachardot}\ {\isasymlbrakk}n\ {\isasymin}\ even{\isacharsemicolon}\ {\isacharhash}{\isadigit{2}}\ dvd\ n{\isasymrbrakk}\ {\isasymLongrightarrow}\ {\isacharhash}{\isadigit{2}}\ dvd\ Suc\ {\isacharparenleft}Suc\ n{\isacharparenright}

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{3}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ even{\isacharunderscore}imp{\isacharunderscore}dvd{\isacharparenright}{\isacharcolon}\isanewline
n\ {\isasymin}\ even\ {\isasymLongrightarrow}\ {\isacharhash}{\isadigit{2}}\ dvd\ n\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}n{\isachardot}\ {\isasymlbrakk}n\ {\isasymin}\ even{\isacharsemicolon}\ {\isasymexists}k{\isachardot}\ n\ {\isacharequal}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ k{\isasymrbrakk}\ {\isasymLongrightarrow}\ {\isasymexists}k{\isachardot}\ Suc\ {\isacharparenleft}Suc\ n{\isacharparenright}\ {\isacharequal}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ k

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{4}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ even{\isacharunderscore}imp{\isacharunderscore}dvd{\isacharparenright}{\isacharcolon}\isanewline
n\ {\isasymin}\ even\ {\isasymLongrightarrow}\ {\isacharhash}{\isadigit{2}}\ dvd\ n\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}n\ k{\isachardot}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ k\ {\isasymin}\ even\ {\isasymLongrightarrow}\ {\isasymexists}ka{\isachardot}\ Suc\ {\isacharparenleft}Suc\ {\isacharparenleft}{\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ k{\isacharparenright}{\isacharparenright}\ {\isacharequal}\ {\isacharhash}{\isadigit{2}}\ {\isacharasterisk}\ ka
*}


text{*no iff-attribute because we don't always want to use it*}
theorem even_iff_dvd: "(n \<in> even) = (#2 dvd n)"
apply (blast intro: dvd_imp_even even_imp_dvd)
done

text{*this result ISN'T inductive...*}
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
oops
text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ Suc{\isacharunderscore}Suc{\isacharunderscore}even{\isacharunderscore}imp{\isacharunderscore}even{\isacharparenright}{\isacharcolon}\isanewline
Suc\ {\isacharparenleft}Suc\ n{\isacharparenright}\ {\isasymin}\ even\ {\isasymLongrightarrow}\ n\ {\isasymin}\ even\isanewline
\ {\isadigit{1}}{\isachardot}\ n\ {\isasymin}\ even\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymAnd}na{\isachardot}\ {\isasymlbrakk}na\ {\isasymin}\ even{\isacharsemicolon}\ n\ {\isasymin}\ even{\isasymrbrakk}\ {\isasymLongrightarrow}\ n\ {\isasymin}\ even
*}


text{*...so we need an inductive lemma...*}
lemma even_imp_even_minus_2: "n \<in> even \<Longrightarrow> n-#2 \<in> even"
apply (erule even.induct)
apply auto
done

text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ even{\isacharunderscore}imp{\isacharunderscore}even{\isacharunderscore}minus{\isacharunderscore}{\isadigit{2}}{\isacharparenright}{\isacharcolon}\isanewline
n\ {\isasymin}\ even\ {\isasymLongrightarrow}\ n\ {\isacharminus}\ {\isacharhash}{\isadigit{2}}\ {\isasymin}\ even\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isadigit{0}}\ {\isacharminus}\ {\isacharhash}{\isadigit{2}}\ {\isasymin}\ even\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymAnd}n{\isachardot}\ {\isasymlbrakk}n\ {\isasymin}\ even{\isacharsemicolon}\ n\ {\isacharminus}\ {\isacharhash}{\isadigit{2}}\ {\isasymin}\ even{\isasymrbrakk}\ {\isasymLongrightarrow}\ Suc\ {\isacharparenleft}Suc\ n{\isacharparenright}\ {\isacharminus}\ {\isacharhash}{\isadigit{2}}\ {\isasymin}\ even
*}


text{*...and prove it in a separate step*}
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (drule even_imp_even_minus_2)
apply simp
done

lemma [iff]: "((Suc (Suc n)) \<in> even) = (n \<in> even)"
apply (blast dest: Suc_Suc_even_imp_even)
done

end

