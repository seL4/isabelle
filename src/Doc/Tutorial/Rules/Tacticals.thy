theory Tacticals imports Main begin

text\<open>REPEAT\<close>
lemma "\<lbrakk>P\<longrightarrow>Q; Q\<longrightarrow>R; R\<longrightarrow>S; P\<rbrakk> \<Longrightarrow> S"
apply (drule mp, assumption)
apply (drule mp, assumption)
apply (drule mp, assumption)
apply (assumption)
done

lemma "\<lbrakk>P\<longrightarrow>Q; Q\<longrightarrow>R; R\<longrightarrow>S; P\<rbrakk> \<Longrightarrow> S"
by (drule mp, assumption)+

text\<open>ORELSE with REPEAT\<close>
lemma "\<lbrakk>Q\<longrightarrow>R; P\<longrightarrow>Q; x<5\<longrightarrow>P;  Suc x < 5\<rbrakk> \<Longrightarrow> R" 
by (drule mp, (assumption|arith))+

text\<open>exercise: what's going on here?\<close>
lemma "\<lbrakk>P\<and>Q\<longrightarrow>R; P\<longrightarrow>Q; P\<rbrakk> \<Longrightarrow> R"
by (drule mp, (intro conjI)?, assumption+)+

text\<open>defer and prefer\<close>

lemma "hard \<and> (P \<or> ~P) \<and> (Q\<longrightarrow>Q)"
apply (intro conjI)   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
defer 1   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply blast+   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
oops

lemma "ok1 \<and> ok2 \<and> doubtful"
apply (intro conjI)   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
prefer 3   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
oops

lemma "bigsubgoal1 \<and> bigsubgoal2 \<and> bigsubgoal3 \<and> bigsubgoal4 \<and> bigsubgoal5 \<and> bigsubgoal6"
apply (intro conjI)   \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
txt\<open>@{subgoals[display,indent=0,margin=65]} 
A total of 6 subgoals...
\<close>
oops



(*needed??*)

lemma "(P\<or>Q) \<and> (R\<or>S) \<Longrightarrow> PP"
apply (elim conjE disjE)
oops

lemma "((P\<or>Q) \<and> R) \<and> (Q \<and> (P\<or>S)) \<Longrightarrow> PP"
apply (elim conjE)
oops

lemma "((P\<or>Q) \<and> R) \<and> (Q \<and> (P\<or>S)) \<Longrightarrow> PP"
apply (erule conjE)+
oops

end
