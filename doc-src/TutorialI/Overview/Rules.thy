theory Rules = Main:

section{*The  Rules of the Game*}


subsection{*Introduction Rules*}

thm impI conjI disjI1 disjI2 iffI

lemma "A \<Longrightarrow> B \<longrightarrow> A \<and> (B \<and> A)"
apply(rule impI)
apply(rule conjI)
 apply assumption
apply(rule conjI)
 apply assumption
apply assumption
done


subsection{*Elimination Rules*}

thm impE mp
thm conjE
thm disjE

lemma disj_swap: "P | Q \<Longrightarrow> Q | P"
apply (erule disjE)
 apply (rule disjI2)
 apply assumption
apply (rule disjI1)
apply assumption
done


subsection{*Destruction Rules*}

thm conjunct1 conjunct1 iffD1 iffD2
lemma conj_swap: "P \<and> Q \<Longrightarrow> Q \<and> P"
apply (rule conjI)
 apply (drule conjunct2)
 apply assumption
apply (drule conjunct1)
apply assumption
done


subsection{*Quantifiers*}


thm allI exI
thm allE exE
thm spec

lemma "\<exists>x.\<forall>y. P x y \<Longrightarrow> \<forall>y.\<exists>x. P x y"
oops

subsection{*Instantiation*}

lemma "\<exists>xs. xs @ xs = xs"
apply(rule_tac x = "[]" in exI)
by simp

lemma "\<forall>xs. f(xs @ xs) = xs \<Longrightarrow> f [] = []"
apply(erule_tac x = "[]" in allE)
by simp


subsection{*Hilbert's epsilon Operator*}

theorem axiom_of_choice:
     "\<forall>x. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
by (fast elim!: someI)


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

thm rev_rev_ident
thm rev_rev_ident[of "[]"]
thm sym
thm sym[OF rev_rev_ident]
thm rev_rev_ident[THEN sym]


subsection{*Further Useful Methods*}

lemma "n \<le> 1 \<and> n \<noteq> 0 \<Longrightarrow> n^n = n"
apply(subgoal_tac "n=1")
 apply simp
apply arith
done


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
oops
end
