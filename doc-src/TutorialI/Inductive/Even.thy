(* ID:         $Id$ *)
theory Even = Main:


consts even :: "nat set"
inductive even
intros
zero[intro!]: "0 \<in> even"
step[intro!]: "n \<in> even \<Longrightarrow> (Suc (Suc n)) \<in> even"

text{*An inductive definition consists of introduction rules. 

@{thm[display] even.step[no_vars]}
\rulename{even.step}

@{thm[display] even.induct[no_vars]}
\rulename{even.induct}

Attributes can be given to the introduction rules.  Here both rules are
specified as \isa{intro!}

Our first lemma states that numbers of the form $2\times k$ are even. *}
lemma two_times_even[intro!]: "#2*k \<in> even"
apply (induct "k")
txt{*
The first step is induction on the natural number \isa{k}, which leaves
two subgoals:
@{subgoals[display,indent=0,margin=65]}
Here \isa{auto} simplifies both subgoals so that they match the introduction
rules, which then are applied automatically.*};
 apply auto
done

text{*Our goal is to prove the equivalence between the traditional definition
of even (using the divides relation) and our inductive definition.  Half of
this equivalence is trivial using the lemma just proved, whose \isa{intro!}
attribute ensures it will be applied automatically.  *}

lemma dvd_imp_even: "#2 dvd n \<Longrightarrow> n \<in> even"
by (auto simp add: dvd_def)

text{*our first rule induction!*}
lemma even_imp_dvd: "n \<in> even \<Longrightarrow> #2 dvd n"
apply (erule even.induct)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply (simp_all add: dvd_def)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply clarify
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply (rule_tac x = "Suc k" in exI, simp)
done


text{*no iff-attribute because we don't always want to use it*}
theorem even_iff_dvd: "(n \<in> even) = (#2 dvd n)"
by (blast intro: dvd_imp_even even_imp_dvd)

text{*this result ISN'T inductive...*}
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
apply (erule even.induct)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
oops

text{*...so we need an inductive lemma...*}
lemma even_imp_even_minus_2: "n \<in> even \<Longrightarrow> n-#2 \<in> even"
apply (erule even.induct)
txt{*
@{subgoals[display,indent=0,margin=65]}
*};
apply auto
done

text{*...and prove it in a separate step*}
lemma Suc_Suc_even_imp_even: "Suc (Suc n) \<in> even \<Longrightarrow> n \<in> even"
by (drule even_imp_even_minus_2, simp)


lemma [iff]: "((Suc (Suc n)) \<in> even) = (n \<in> even)"
by (blast dest: Suc_Suc_even_imp_even)

end

