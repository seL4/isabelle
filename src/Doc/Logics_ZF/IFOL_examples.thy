section\<open>Examples of Intuitionistic Reasoning\<close>

theory IFOL_examples imports IFOL begin

text\<open>Quantifier example from the book Logic and Computation\<close>
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule impI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule allI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule exI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule exE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule allE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
txt\<open>Now \<open>apply assumption\<close> fails\<close>
oops

text\<open>Trying again, with the same first two steps\<close>
lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule impI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule allI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule exE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule exI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule allE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
done

lemma "(EX y. ALL x. Q(x,y)) -->  (ALL x. EX y. Q(x,y))"
by (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)

text\<open>Example of Dyckhoff's method\<close>
lemma "~ ~ ((P-->Q) | (Q-->P))"
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (unfold not_def)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (rule impI)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule disj_impE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply (erule imp_impE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
 apply (erule imp_impE)
  \<comment> \<open>@{subgoals[display,indent=0,margin=65]}\<close>
apply assumption 
apply (erule FalseE)+
done

end
