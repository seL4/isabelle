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

text {*
substitution

@{thm[display] ssubst}
\rulename{ssubst}
*};

lemma "\<lbrakk> x = f x; P(f x) \<rbrakk> \<Longrightarrow> P x"
apply (erule ssubst)
apply assumption
done

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

lemma "\<lbrakk> x = f x; P (f x) (f x) x \<rbrakk> \<Longrightarrow> P x x x"
apply (erule_tac P="\<lambda>u. P u u x" in ssubst);
apply assumption
done


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
apply (erule notE, assumption)
done


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

apply (erule contrapos_np, rule conjI)
txt{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{6}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}P\ {\isasymor}\ Q{\isacharparenright}\ {\isasymand}\ R\ {\isasymLongrightarrow}\ P\ {\isasymor}\ Q\ {\isasymand}\ R\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ Q\isanewline
\ {\isadigit{2}}{\isachardot}\ {\isasymlbrakk}R{\isacharsemicolon}\ Q{\isacharsemicolon}\ {\isasymnot}\ P{\isasymrbrakk}\ {\isasymLongrightarrow}\ R
*}

  apply assumption
 apply assumption
done



text{*Quantifiers*}

lemma "\<forall>x. P x \<longrightarrow> P x"
apply (rule allI)
apply (rule impI)
apply assumption
done

lemma "(\<forall>x. P \<longrightarrow> Q x) \<Longrightarrow> P \<longrightarrow> (\<forall>x. Q x)"
apply (rule impI)
apply (rule allI)
apply (drule spec)
apply (drule mp)
  apply assumption
 apply assumption
done

lemma "\<lbrakk>\<forall>x. P x \<longrightarrow> P (f x); P a\<rbrakk> \<Longrightarrow> P(f (f a))"
apply (frule spec)
apply (drule mp, assumption)
apply (drule spec)
apply (drule mp, assumption, assumption)
done

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
