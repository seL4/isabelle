(*<*)theory Rules = Main:(*>*)

section{*The Rules of the Game*}


subsection{*Introduction Rules*}

text{* Introduction rules for propositional logic:
\begin{center}
\begin{tabular}{ll}
@{thm[source]impI} & @{thm impI[no_vars]} \\
@{thm[source]conjI} & @{thm conjI[no_vars]} \\
@{thm[source]disjI1} & @{thm disjI1[no_vars]} \\
@{thm[source]disjI2} & @{thm disjI2[no_vars]} \\
@{thm[source]iffI} & @{thm iffI[no_vars]}
\end{tabular}
\end{center}
*}

(*<*)thm impI conjI disjI1 disjI2 iffI(*>*)

lemma "A \<Longrightarrow> B \<longrightarrow> A \<and> (B \<and> A)"
apply(rule impI)
apply(rule conjI)
 apply assumption
apply(rule conjI)
 apply assumption
apply assumption
done


subsection{*Elimination Rules*}

text{* Elimination rules for propositional logic:
\begin{center}
\begin{tabular}{ll}
@{thm[source]impE} & @{thm impE[no_vars]} \\
@{thm[source]mp} & @{thm mp[no_vars]} \\
@{thm[source]conjE} & @{thm conjE[no_vars]} \\
@{thm[source]disjE} & @{thm disjE[no_vars]}
\end{tabular}
\end{center}
*}
(*<*)
thm impE mp
thm conjE
thm disjE
(*>*)
lemma disj_swap: "P \<or> Q \<Longrightarrow> Q \<or> P"
apply (erule disjE)
 apply (rule disjI2)
 apply assumption
apply (rule disjI1)
apply assumption
done


subsection{*Destruction Rules*}

text{* Destruction rules for propositional logic:
\begin{center}
\begin{tabular}{ll}
@{thm[source]conjunct1} & @{thm conjunct1[no_vars]} \\
@{thm[source]conjunct2} & @{thm conjunct2[no_vars]} \\
@{thm[source]iffD1} & @{thm iffD1[no_vars]} \\
@{thm[source]iffD2} & @{thm iffD2[no_vars]}
\end{tabular}
\end{center}
*}

(*<*)thm conjunct1 conjunct1 iffD1 iffD2(*>*)

lemma conj_swap: "P \<and> Q \<Longrightarrow> Q \<and> P"
apply (rule conjI)
 apply (drule conjunct2)
 apply assumption
apply (drule conjunct1)
apply assumption
done


subsection{*Quantifiers*}

text{* Quantifier rules:
\begin{center}
\begin{tabular}{ll}
@{thm[source]allI} & @{thm allI[no_vars]} \\
@{thm[source]exI} & @{thm exI[no_vars]} \\
@{thm[source]allE} & @{thm allE[no_vars]} \\
@{thm[source]exE} & @{thm exE[no_vars]} \\
@{thm[source]spec} & @{thm spec[no_vars]}
\end{tabular}
\end{center}
*}
(*<*)
thm allI exI
thm allE exE
thm spec
(*>*)
lemma "\<exists>x.\<forall>y. P x y \<Longrightarrow> \<forall>y.\<exists>x. P x y"
(*<*)oops(*>*)

subsection{*Instantiation*}

lemma "\<exists>xs. xs @ xs = xs"
apply(rule_tac x = "[]" in exI)
by simp

lemma "\<forall>xs. f(xs @ xs) = xs \<Longrightarrow> f [] = []"
apply(erule_tac x = "[]" in allE)
by simp


subsection{*Automation*}

lemma "(\<forall>x. honest(x) \<and> industrious(x) \<longrightarrow> healthy(x)) \<and>  
       \<not> (\<exists>x. grocer(x) \<and> healthy(x)) \<and> 
       (\<forall>x. industrious(x) \<and> grocer(x) \<longrightarrow> honest(x)) \<and> 
       (\<forall>x. cyclist(x) \<longrightarrow> industrious(x)) \<and> 
       (\<forall>x. \<not>healthy(x) \<and> cyclist(x) \<longrightarrow> \<not>honest(x))  
       \<longrightarrow> (\<forall>x. grocer(x) \<longrightarrow> \<not>cyclist(x))";
by blast

lemma "(\<Union>i\<in>I. A(i)) \<inter> (\<Union>j\<in>J. B(j)) =
       (\<Union>i\<in>I. \<Union>j\<in>J. A(i) \<inter> B(j))"
by fast

lemma "\<exists>x.\<forall>y. P x y \<Longrightarrow> \<forall>y.\<exists>x. P x y"
apply(clarify)
by blast


subsection{*Forward Proof*}

text{*
Instantiation of unknowns (in left-to-right order):
\begin{center}
\begin{tabular}{@ {}ll@ {}}
@{thm[source]append_self_conv} & @{thm append_self_conv} \\
@{thm[source]append_self_conv[of _ "[]"]} & @{thm append_self_conv[of _ "[]"]}
\end{tabular}
\end{center}
Applying one theorem to another
by unifying the premise of one theorem with the conclusion of another:
\begin{center}
\begin{tabular}{@ {}ll@ {}}
@{thm[source]sym} & @{thm sym} \\
@{thm[source]sym[OF append_self_conv]} & @{thm sym[OF append_self_conv]}\\
@{thm[source]append_self_conv[THEN sym]} & @{thm append_self_conv[THEN sym]}
\end{tabular}
\end{center}
*}
(*<*)
thm append_self_conv
thm append_self_conv[of _ "[]"]
thm sym
thm sym[OF append_self_conv]
thm append_self_conv[THEN sym]
(*>*)
subsection{*Further Useful Methods*}

lemma "n \<le> 1 \<and> n \<noteq> 0 \<Longrightarrow> n^n = n"
apply(subgoal_tac "n=1")
 apply simp
apply arith
done

text{* And a cute example: *}
lemma "\<lbrakk> 2 \<in> Q; sqrt 2 \<notin> Q;
         \<forall>x y z. sqrt x * sqrt x = x \<and>
                  x ^ 2 = x * x \<and>
                 (x ^ y) ^ z = x ^ (y*z)
       \<rbrakk> \<Longrightarrow> \<exists>a b. a \<notin> Q \<and> b \<notin> Q \<and> a ^ b \<in> Q"
(*
apply(case_tac "")
 apply blast
apply(rule_tac x = "" in exI)
apply(rule_tac x = "" in exI)
apply simp
done
*)
(*<*)oops

end(*>*)
