(* ID:         $Id$ *)
theory Basic = Main:

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

text {*NEW
by eliminates uses of assumption and done
*}

lemma imp_uncurry: "P \<longrightarrow> Q \<longrightarrow> R \<Longrightarrow> P \<and> Q \<longrightarrow> R"
apply (rule impI)
apply (erule conjE)
apply (drule mp)
 apply assumption
by (drule mp)


text {*
substitution

@{thm[display] ssubst}
\rulename{ssubst}
*};

lemma "\<lbrakk> x = f x; P(f x) \<rbrakk> \<Longrightarrow> P x"
by (erule ssubst)

text {*
also provable by simp (re-orients)
*};

lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
apply (erule ssubst)
back
back
back
back
apply assumption
done

text {*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}x\ {\isacharequal}\ f\ x{\isacharsemicolon}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ x\ x\isanewline
\ \isadigit{1}{\isachardot}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}x\ {\isacharequal}\ f\ x{\isacharsemicolon}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ x\ x\isanewline
\ \isadigit{1}{\isachardot}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isasymLongrightarrow}\ P\ x\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}x\ {\isacharequal}\ f\ x{\isacharsemicolon}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ x\ x\isanewline
\ \isadigit{1}{\isachardot}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isacharparenleft}f\ x{\isacharparenright}

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}x\ {\isacharequal}\ f\ x{\isacharsemicolon}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ x\ x\isanewline
\ \isadigit{1}{\isachardot}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isasymLongrightarrow}\ P\ x\ x\ {\isacharparenleft}f\ x{\isacharparenright}

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}x\ {\isacharequal}\ f\ x{\isacharsemicolon}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ x\ x\isanewline
\ \isadigit{1}{\isachardot}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}\ {\isacharparenleft}f\ x{\isacharparenright}\ x
*};

lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
apply (erule ssubst, assumption)
done

text{*
or better still NEW
*}

lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
by (erule ssubst)


text{*NEW*}
lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
apply (erule_tac P="\<lambda>u. P u u x" in ssubst)
apply (assumption)
done


lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
by (erule_tac P="\<lambda>u. P u u x" in ssubst)


text {*
negation

@{thm[display] notI}
\rulename{notI}

@{thm[display] notE}
\rulename{notE}

@{thm[display] classical}
\rulename{classical}

@{thm[display] contrapos_pp}
\rulename{contrapos_pp}

@{thm[display] contrapos_np}
\rulename{contrapos_np}

@{thm[display] contrapos_nn}
\rulename{contrapos_nn}
*};


lemma "\<lbrakk>\<not>(P\<longrightarrow>Q); \<not>(R\<longrightarrow>Q)\<rbrakk> \<Longrightarrow> R"
apply (erule_tac Q="R\<longrightarrow>Q" in contrapos_np)
txt{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}{\isasymnot}\ {\isacharparenleft}P\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isacharsemicolon}\ {\isasymnot}\ {\isacharparenleft}R\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isasymnot}\ {\isacharparenleft}P\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isacharsemicolon}\ {\isasymnot}\ R{\isasymrbrakk}\ {\isasymLongrightarrow}\ R\ {\isasymlongrightarrow}\ Q
*}

apply intro
txt{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{3}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}{\isasymnot}\ {\isacharparenleft}P\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isacharsemicolon}\ {\isasymnot}\ {\isacharparenleft}R\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isasymnot}\ {\isacharparenleft}P\ {\isasymlongrightarrow}\ Q{\isacharparenright}{\isacharsemicolon}\ {\isasymnot}\ R{\isacharsemicolon}\ R{\isasymrbrakk}\ {\isasymLongrightarrow}\ Q
*}
by (erule notE)
text{*NEW*}



lemma "(P \<or> Q) \<and> R \<Longrightarrow> P \<or> Q \<and> R"
apply intro
txt{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R\ {\isasymLongrightarrow}\ P\ {\isasymor}\ Q\ {\isasymand}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R{\isacharsemicolon}\ {\isasymnot}\ {\isacharparenleft}Q\ {\isasymand}\ R{\isacharparenright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ P
*}

apply (elim conjE disjE)
 apply assumption

txt{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{4}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R\ {\isasymLongrightarrow}\ P\ {\isasymor}\ Q\ {\isasymand}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isasymnot}\ {\isacharparenleft}Q\ {\isasymand}\ R{\isacharparenright}{\isacharsemicolon}\ R{\isacharsemicolon}\ Q{\isasymrbrakk}\ {\isasymLongrightarrow}\ P
*}

by (erule contrapos_np, rule conjI)
text{*NEW
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{6}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R\ {\isasymLongrightarrow}\ P\ {\isasymor}\ Q\ {\isasymand}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ Q\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ R
*}


text{*Quantifiers*}

lemma "\<forall>x. P x \<longrightarrow> P x"
apply (rule allI)
by (rule impI)
text{*NEW*}

lemma "(\<forall>x. P \<longrightarrow> Q x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. Q x)"
apply (rule impI, rule allI)
apply (drule spec)
by (drule mp)
text{*NEW*}

lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (h x); P a\<rbrakk> \<Longrightarrow> P(h (h a))"
apply (frule spec)
apply (drule mp, assumption)
apply (drule spec)
by (drule mp)
text{*NEW*}


text
{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}{\isasymforall}x{\isachardot}\ P\ x\ {\isasymlongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}{\isacharsemicolon}\ P\ a{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ {\isacharparenleft}f\ a{\isacharparenright}{\isacharparenright}\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isasymforall}x{\isachardot}\ P\ x\ {\isasymlongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}{\isacharsemicolon}\ P\ a{\isacharsemicolon}\ P\ {\isacharquery}x\ {\isasymlongrightarrow}\ P\ {\isacharparenleft}f\ {\isacharquery}x{\isacharparenright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ {\isacharparenleft}f\ a{\isacharparenright}{\isacharparenright}
*}

text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{3}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}{\isasymforall}x{\isachardot}\ P\ x\ {\isasymlongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}{\isacharsemicolon}\ P\ a{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ {\isacharparenleft}f\ a{\isacharparenright}{\isacharparenright}\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}{\isasymforall}x{\isachardot}\ P\ x\ {\isasymlongrightarrow}\ P\ {\isacharparenleft}f\ x{\isacharparenright}{\isacharsemicolon}\ P\ a{\isacharsemicolon}\ P\ {\isacharparenleft}f\ a{\isacharparenright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}f\ {\isacharparenleft}f\ a{\isacharparenright}{\isacharparenright}
*}

lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (f x); P a\<rbrakk> \<Longrightarrow> P(f (f a))"
by blast

text{*NEW
Hilbert-epsilon theorems*}

text{*
@{thm[display] some_equality[no_vars]}
\rulename{some_equality}

@{thm[display] someI[no_vars]}
\rulename{someI}

@{thm[display] someI2[no_vars]}
\rulename{someI2}

needed for examples

@{thm[display] inv_def[no_vars]}
\rulename{inv_def}

@{thm[display] Least_def[no_vars]}
\rulename{Least_def}

@{thm[display] order_antisym[no_vars]}
\rulename{order_antisym}
*}


lemma "inv Suc (Suc x) = x"
by (simp add: inv_def)

text{*but we know nothing about inv Suc 0*}

theorem Least_equality:
     "\<lbrakk> P (k::nat);  \<forall>x. P x \<longrightarrow> k \<le> x \<rbrakk> \<Longrightarrow> (LEAST x. P(x)) = k"
apply (simp add: Least_def)
 
txt{*omit maybe?
@{subgoals[display,indent=0,margin=65]}
*};
   
apply (rule some_equality)

txt{*
@{subgoals[display,indent=0,margin=65]}

first subgoal is existence; second is uniqueness
*};
by (auto intro: order_antisym)


theorem axiom_of_choice:
     "(\<forall>x. \<exists> y. P x y) \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
apply (rule exI, rule allI)

txt{*
@{subgoals[display,indent=0,margin=65]}

state after intro rules
*};
apply (drule spec, erule exE)

txt{*
@{subgoals[display,indent=0,margin=65]}

applying @text{someI} automatically instantiates
@{term f} to @{term "\<lambda>x. SOME y. P x y"}
*};

by (rule someI)

(*both can be done by blast, which however hasn't been introduced yet*)
lemma "[| P (k::nat);  \<forall>x. P x \<longrightarrow> k \<le> x |] ==> (LEAST x. P(x)) = k";
apply (simp add: Least_def)
by (blast intro: some_equality order_antisym);

theorem axiom_of_choice: "(\<forall>x. \<exists> y. P x y) \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
apply (rule exI [of _  "\<lambda>x. SOME y. P x y"])
by (blast intro: someI);

text{*end of NEW material*}

lemma "(\<exists>x. P x) \<or> (\<exists>x. Q x) \<Longrightarrow> \<exists>x. P x \<or> Q x"
apply elim
 apply intro
 apply assumption
apply (intro exI disjI2) (*or else we get disjCI*)
apply assumption
done

lemma "(P\<longrightarrow>Q) \<or> (Q\<longrightarrow>P)"
apply intro
apply elim
apply assumption
done

lemma "(P\<or>Q)\<and>(P\<or>R) \<Longrightarrow> P \<or> (Q\<and>R)"
apply intro
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

lemma "\<forall> z. R z z \<Longrightarrow> \<exists>x. \<forall> y. R x y"
apply (rule exI)
apply (rule allI)
apply (drule spec)
oops

lemma "\<forall>x. \<exists> y. x=y"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma "\<exists>x. \<forall> y. x=y"
apply (rule exI)
apply (rule allI)
oops

end
