section\<open>Examples of Classical Reasoning\<close>

theory FOL_examples imports FOL begin

lemma "EX y. ALL x. P(y)-->P(x)"
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule exCI)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule allI)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule impI)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule allE)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
txt\<open>see below for @{text allI} combined with @{text swap}\<close>
apply (erule allI [THEN [2] swap])
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule impI)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule notE)
  \<comment>\<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption
done

text \<open>
@{thm[display] allI [THEN [2] swap]}
\<close>

lemma "EX y. ALL x. P(y)-->P(x)"
by blast

end


