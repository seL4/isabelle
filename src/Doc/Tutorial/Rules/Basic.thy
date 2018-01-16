theory Basic imports Main begin

lemma conj_rule: "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P)"
apply (rule conjI)
 apply assumption
apply (rule conjI)
 apply assumption
apply assumption
done
    

lemma disj_swap: "P | Q \<Longrightarrow> Q | P"
apply (erule disjE)
 apply (rule disjI2)
 apply assumption
apply (rule disjI1)
apply assumption
done

lemma conj_swap: "P \<and> Q \<Longrightarrow> Q \<and> P"
apply (rule conjI)
 apply (drule conjunct2)
 apply assumption
apply (drule conjunct1)
apply assumption
done

lemma imp_uncurry: "P \<longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<and> Q \<longrightarrow> R"
apply (rule impI)
apply (erule conjE)
apply (drule mp)
 apply assumption
apply (drule mp)
  apply assumption
 apply assumption
done

text \<open>
by eliminates uses of assumption and done
\<close>

lemma imp_uncurry': "P \<longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<and> Q \<longrightarrow> R"
apply (rule impI)
apply (erule conjE)
apply (drule mp)
 apply assumption
by (drule mp)


text \<open>
substitution

@{thm[display] ssubst}
\rulename{ssubst}
\<close>

lemma "\<lbrakk> x = f x; P(f x) \<rbrakk> \<Longrightarrow> P x"
by (erule ssubst)

text \<open>
also provable by simp (re-orients)
\<close>

text \<open>
the subst method

@{thm[display] mult.commute}
\rulename{mult.commute}

this would fail:
apply (simp add: mult.commute) 
\<close>


lemma "\<lbrakk>P x y z; Suc x < y\<rbrakk> \<Longrightarrow> f z = x*y"
txt\<open>
@{subgoals[display,indent=0,margin=65]}
\<close>
apply (subst mult.commute) 
txt\<open>
@{subgoals[display,indent=0,margin=65]}
\<close>
oops

(*exercise involving THEN*)
lemma "\<lbrakk>P x y z; Suc x < y\<rbrakk> \<Longrightarrow> f z = x*y"
apply (rule mult.commute [THEN ssubst]) 
oops


lemma "\<lbrakk>x = f x; triple (f x) (f x) x\<rbrakk> \<Longrightarrow> triple x x x"
apply (erule ssubst) 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
back \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
back \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
back \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
back \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption
done

lemma "\<lbrakk> x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
apply (erule ssubst, assumption)
done

text\<open>
or better still 
\<close>

lemma "\<lbrakk> x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
by (erule ssubst)


lemma "\<lbrakk> x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
apply (erule_tac P="\<lambda>u. triple u u x" in ssubst)
apply (assumption)
done


lemma "\<lbrakk> x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
by (erule_tac P="\<lambda>u. triple u u x" in ssubst)


text \<open>
negation

@{thm[display] notI}
\rulename{notI}

@{thm[display] notE}
\rulename{notE}

@{thm[display] classical}
\rulename{classical}

@{thm[display] contrapos_pp}
\rulename{contrapos_pp}

@{thm[display] contrapos_pn}
\rulename{contrapos_pn}

@{thm[display] contrapos_np}
\rulename{contrapos_np}

@{thm[display] contrapos_nn}
\rulename{contrapos_nn}
\<close>


lemma "\<lbrakk>\<not>(P\<longrightarrow>Q); \<not>(R\<longrightarrow>Q)\<rbrakk> \<Longrightarrow> R"
apply (erule_tac Q="R\<longrightarrow>Q" in contrapos_np)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (intro impI)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
by (erule notE)

text \<open>
@{thm[display] disjCI}
\rulename{disjCI}
\<close>

lemma "(P \<or> Q) \<and> R \<Longrightarrow> P \<or> Q \<and> R"
apply (intro disjCI conjI)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>

apply (elim conjE disjE)
 apply assumption
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>

by (erule contrapos_np, rule conjI)
text\<open>
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{6}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R\ {\isasymLongrightarrow}\ P\ {\isasymor}\ Q\ {\isasymand}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ Q\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ R
\<close>


text\<open>rule_tac, etc.\<close>


lemma "P&Q"
apply (rule_tac P=P and Q=Q in conjI)
oops


text\<open>unification failure trace\<close>

declare [[unify_trace_failure = true]]

lemma "P(a, f(b, g(e,a), b), a) \<Longrightarrow> P(a, f(b, g(c,a), b), a)"
txt\<open>
@{subgoals[display,indent=0,margin=65]}
apply assumption
Clash: e =/= c

Clash: == =/= Trueprop
\<close>
oops

lemma "\<forall>x y. P(x,y) --> P(y,x)"
apply auto
txt\<open>
@{subgoals[display,indent=0,margin=65]}
apply assumption

Clash: bound variable x (depth 1) =/= bound variable y (depth 0)

Clash: == =/= Trueprop
Clash: == =/= Trueprop
\<close>
oops

declare [[unify_trace_failure = false]]


text\<open>Quantifiers\<close>

text \<open>
@{thm[display] allI}
\rulename{allI}

@{thm[display] allE}
\rulename{allE}

@{thm[display] spec}
\rulename{spec}
\<close>

lemma "\<forall>x. P x \<longrightarrow> P x"
apply (rule allI)
by (rule impI)

lemma "(\<forall>x. P \<longrightarrow> Q x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. Q x)"
apply (rule impI, rule allI)
apply (drule spec)
by (drule mp)

text\<open>rename_tac\<close>
lemma "x < y \<Longrightarrow> \<forall>x y. P x (f y)"
apply (intro allI)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rename_tac v w)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
oops


lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (h x); P a\<rbrakk> \<Longrightarrow> P(h (h a))"
apply (frule spec)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (drule mp, assumption)
apply (drule spec)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
by (drule mp)

lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (f x); P a\<rbrakk> \<Longrightarrow> P(f (f a))"
by blast


text\<open>
the existential quantifier\<close>

text \<open>
@{thm[display]"exI"}
\rulename{exI}

@{thm[display]"exE"}
\rulename{exE}
\<close>


text\<open>
instantiating quantifiers explicitly by rule_tac and erule_tac\<close>

lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (h x); P a\<rbrakk> \<Longrightarrow> P(h (h a))"
apply (frule spec)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (drule mp, assumption)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (drule_tac x = "h a" in spec)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
by (drule mp)

text \<open>
@{thm[display]"dvd_def"}
\rulename{dvd_def}
\<close>

lemma mult_dvd_mono: "\<lbrakk>i dvd m; j dvd n\<rbrakk> \<Longrightarrow> i*j dvd (m*n :: nat)"
apply (simp add: dvd_def)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule exE) 
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule exE) 
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rename_tac l)
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule_tac x="k*l" in exI) 
        \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply simp
done

text\<open>
Hilbert-epsilon theorems\<close>

text\<open>
@{thm[display] the_equality[no_vars]}
\rulename{the_equality}

@{thm[display] some_equality[no_vars]}
\rulename{some_equality}

@{thm[display] someI[no_vars]}
\rulename{someI}

@{thm[display] someI2[no_vars]}
\rulename{someI2}

@{thm[display] someI_ex[no_vars]}
\rulename{someI_ex}

needed for examples

@{thm[display] inv_def[no_vars]}
\rulename{inv_def}

@{thm[display] Least_def[no_vars]}
\rulename{Least_def}

@{thm[display] order_antisym[no_vars]}
\rulename{order_antisym}
\<close>


lemma "inv Suc (Suc n) = n"
by (simp add: inv_def)

text\<open>but we know nothing about inv Suc 0\<close>

theorem Least_equality:
     "\<lbrakk> P (k::nat);  \<forall>x. P x \<longrightarrow> k \<le> x \<rbrakk> \<Longrightarrow> (LEAST x. P(x)) = k"
apply (simp add: Least_def)
 
txt\<open>
@{subgoals[display,indent=0,margin=65]}
\<close>
   
apply (rule the_equality)

txt\<open>
@{subgoals[display,indent=0,margin=65]}

first subgoal is existence; second is uniqueness
\<close>
by (auto intro: order_antisym)


theorem axiom_of_choice:
     "(\<forall>x. \<exists>y. P x y) \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
apply (rule exI, rule allI)

txt\<open>
@{subgoals[display,indent=0,margin=65]}

state after intro rules
\<close>
apply (drule spec, erule exE)

txt\<open>
@{subgoals[display,indent=0,margin=65]}

applying @text{someI} automatically instantiates
@{term f} to @{term "\<lambda>x. SOME y. P x y"}
\<close>

by (rule someI)

(*both can be done by blast, which however hasn't been introduced yet*)
lemma "[| P (k::nat);  \<forall>x. P x \<longrightarrow> k \<le> x |] ==> (LEAST x. P(x)) = k"
apply (simp add: Least_def)
by (blast intro: order_antisym)

theorem axiom_of_choice': "(\<forall>x. \<exists>y. P x y) \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
apply (rule exI [of _  "\<lambda>x. SOME y. P x y"])
by (blast intro: someI)

text\<open>end of Epsilon section\<close>


lemma "(\<exists>x. P x) \<or> (\<exists>x. Q x) \<Longrightarrow> \<exists>x. P x \<or> Q x"
apply (elim exE disjE)
 apply (intro exI disjI1)
 apply assumption
apply (intro exI disjI2)
apply assumption
done

lemma "(P\<longrightarrow>Q) \<or> (Q\<longrightarrow>P)"
apply (intro disjCI impI)
apply (elim notE)
apply (intro impI)
apply assumption
done

lemma "(P\<or>Q)\<and>(P\<or>R) \<Longrightarrow> P \<or> (Q\<and>R)"
apply (intro disjCI conjI)
apply (elim conjE disjE)
apply blast
apply blast
apply blast
apply blast
(*apply elim*)
done

lemma "(\<exists>x. P \<and> Q x) \<Longrightarrow> P \<and> (\<exists>x. Q x)"
apply (erule exE)
apply (erule conjE)
apply (rule conjI)
 apply assumption
apply (rule exI)
 apply assumption
done

lemma "(\<exists>x. P x) \<and> (\<exists>x. Q x) \<Longrightarrow> \<exists>x. P x \<and> Q x"
apply (erule conjE)
apply (erule exE)
apply (erule exE)
apply (rule exI)
apply (rule conjI)
 apply assumption
oops

lemma "\<forall>y. R y y \<Longrightarrow> \<exists>x. \<forall>y. R x y"
apply (rule exI) 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule allI) 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (drule spec) 
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
oops

lemma "\<forall>x. \<exists>y. x=y"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma "\<exists>x. \<forall>y. x=y"
apply (rule exI)
apply (rule allI)
oops

end
