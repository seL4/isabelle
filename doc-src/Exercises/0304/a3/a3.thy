
(*<*) theory a3 = Main: (*>*)

subsection {* Natural deduction -- Propositional Logic \label{psv0304a3} *}

text {* In this exercise, we will prove some lemmas of propositional
logic with the aid of a calculus of natural deduction.

For the proofs, you may only use

\begin{itemize}
\item the following lemmas: \\
@{text "notI:"}~@{thm notI[of A,no_vars]},\\
@{text "notE:"}~@{thm notE[of A B,no_vars]},\\
@{text "conjI:"}~@{thm conjI[of A B,no_vars]},\\ 
@{text "conjE:"}~@{thm conjE[of A B C,no_vars]},\\
@{text "disjI1:"}~@{thm disjI1[of A B,no_vars]},\\
@{text "disjI2:"}~@{thm disjI2[of A B,no_vars]},\\
@{text "disjE:"}~@{thm disjE[of A B C,no_vars]},\\
@{text "impI:"}~@{thm impI[of A B,no_vars]},\\
@{text "impE:"}~@{thm impE[of A B C,no_vars]},\\
@{text "mp:"}~@{thm mp[of A B,no_vars]}\\
@{text "iffI:"}~@{thm iffI[of A B,no_vars]}, \\
@{text "iffE:"}~@{thm iffE[of A B C,no_vars]}\\
@{text "classical:"}~@{thm classical[of A,no_vars]}

\item the proof methods @{term rule}, @{term erule} and @{term assumption}
\end{itemize}
*}

lemma I: "A \<longrightarrow> A"
(*<*) oops (*>*)

lemma "A \<and> B \<longrightarrow> B \<and> A"
(*<*) oops (*>*)

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
(*<*) oops (*>*)

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
(*<*) oops (*>*)

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
(*<*) oops (*>*)

lemma "(A \<or> A) = (A \<and> A)"
(*<*) oops (*>*)

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
(*<*) oops (*>*)

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
(*<*) oops (*>*)

lemma "\<not> \<not> A \<longrightarrow> A"
(*<*) oops (*>*)

lemma "A \<longrightarrow> \<not> \<not> A"
(*<*) oops (*>*)

lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
(*<*) oops (*>*)

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
(*<*) oops (*>*)

lemma "A \<or> \<not> A"
(*<*) oops (*>*)

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
(*<*) oops (*>*)

(*<*) end (*>*)

